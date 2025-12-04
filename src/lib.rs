#![doc = include_str!("../README.md")]

pub mod sys;

use bitflags::bitflags;
use camino::{Utf8Path, Utf8PathBuf};
use std::ffi::{CStr, CString};
use std::io;
use std::mem::MaybeUninit;
use std::os::unix::io::{AsRawFd, RawFd};
use std::time::Duration;
use thiserror::Error;

/// Error returned by [`EventPort::new`].
#[derive(Debug, Error)]
#[error("failed to create event port")]
pub struct PortCreateError(#[source] pub io::Error);

/// Error returned by [`EventPort::associate_fd`].
#[derive(Debug, Error)]
#[error("failed to associate fd {fd} with port")]
pub struct AssociateFdError {
    pub fd: RawFd,
    #[source]
    pub source: io::Error,
}

/// Error returned by [`EventPort::dissociate_fd`].
#[derive(Debug, Error)]
#[error("failed to dissociate fd {fd} from port")]
pub struct DissociateFdError {
    pub fd: RawFd,
    #[source]
    pub source: io::Error,
}

/// Error returned by [`EventPort::associate_file`].
#[derive(Debug, Error)]
#[error("failed to associate file '{path}' with port")]
pub struct AssociateFileError {
    pub path: Utf8PathBuf,
    #[source]
    pub source: io::Error,
}

/// Error returned by [`EventPort::dissociate_file`].
#[derive(Debug, Error)]
#[error("failed to dissociate file '{path}' from port")]
pub struct DissociateFileError {
    pub path: Utf8PathBuf,
    #[source]
    pub source: io::Error,
}

/// Error returned by [`EventPort::send`].
#[derive(Debug, Error)]
#[error("failed to send user event to port")]
pub struct SendError(#[source] pub io::Error);

/// Error returned by [`EventPort::get`].
#[derive(Debug, Error)]
#[error("failed to get event from port")]
pub struct GetError(#[source] pub io::Error);

/// Error returned by [`EventPort::get_n`].
#[derive(Debug, Error)]
#[error("failed to get events from port")]
pub struct GetNError(#[source] pub io::Error);

/// Error returned by [`FileObj::new`] and [`FileObj::new_nofollow`].
#[derive(Debug, Error)]
pub enum FileObjError {
    #[error("path '{path}' contains interior null bytes")]
    InvalidPath {
        path: Utf8PathBuf,
        #[source]
        source: std::ffi::NulError,
    },
    #[error("failed to stat '{path}'")]
    Stat {
        path: Utf8PathBuf,
        #[source]
        source: io::Error,
    },
}

/// Error returned by [`FileObj::refresh`].
#[derive(Debug, Error)]
#[error("failed to refresh metadata for '{path}'")]
pub struct RefreshError {
    pub path: Utf8PathBuf,
    #[source]
    pub source: io::Error,
}

/// Error returned by [`PortEvent::as_file_obj`].
#[derive(Debug, Error)]
pub enum ExtractFileObjError {
    #[error("null file object pointer in event")]
    NullPointer,
    #[error("path contains interior null bytes")]
    InvalidPath(#[source] std::ffi::NulError),
}

bitflags! {
    /// Poll event flags for file descriptor monitoring.
    ///
    /// These flags are used with `EventPort::associate_fd()` to specify which
    /// events to monitor on a file descriptor.
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    pub struct PollEvents: i32 {
        /// Data available to read (normal data)
        const IN = libc::POLLIN as i32;
        /// Data available to read (priority data)
        const RDNORM = libc::POLLRDNORM as i32;
        /// Ready for writing (normal data)
        const OUT = libc::POLLOUT as i32;
        /// Ready for writing (priority data)
        const WRNORM = libc::POLLWRNORM as i32;
        /// Error condition
        const ERR = libc::POLLERR as i32;
        /// Hang up
        const HUP = libc::POLLHUP as i32;
        /// Invalid request
        const NVAL = libc::POLLNVAL as i32;
    }
}

impl std::fmt::Display for PollEvents {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut flags = Vec::new();
        if self.contains(PollEvents::IN) {
            flags.push("In");
        }
        if self.contains(PollEvents::RDNORM) {
            flags.push("RdNorm");
        }
        if self.contains(PollEvents::OUT) {
            flags.push("Out");
        }
        if self.contains(PollEvents::WRNORM) {
            flags.push("WrNorm");
        }
        if self.contains(PollEvents::ERR) {
            flags.push("Err");
        }
        if self.contains(PollEvents::HUP) {
            flags.push("Hup");
        }
        if self.contains(PollEvents::NVAL) {
            flags.push("Nval");
        }

        if flags.is_empty() {
            write!(f, "(empty)")
        } else {
            write!(f, "{}", flags.join(" | "))
        }
    }
}

bitflags! {
    /// File system event flags for file monitoring.
    ///
    /// These flags are used with `EventPort::associate_file()` to specify which
    /// file system events to monitor. Exception events (DELETE, RENAME_*, UNMOUNTED,
    /// MOUNTEDOVER) are always delivered and cannot be filtered.
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    pub struct FileEvents: i32 {
        /// File access time changed
        const ACCESS = sys::FILE_ACCESS as i32;
        /// File modification time changed
        const MODIFIED = sys::FILE_MODIFIED as i32;
        /// File attributes changed
        const ATTRIB = sys::FILE_ATTRIB as i32;
        /// File was truncated
        const TRUNC = sys::FILE_TRUNC as i32;
        /// Do not follow symbolic links
        const NOFOLLOW = sys::FILE_NOFOLLOW as i32;
        /// File was deleted (always delivered)
        const DELETE = sys::FILE_DELETE as i32;
        /// File was renamed to this name (always delivered)
        const RENAME_TO = sys::FILE_RENAME_TO as i32;
        /// File was renamed from this name (always delivered)
        const RENAME_FROM = sys::FILE_RENAME_FROM as i32;
        /// File system was unmounted (always delivered)
        const UNMOUNTED = sys::UNMOUNTED as i32;
        /// File was mounted over (always delivered)
        const MOUNTEDOVER = sys::MOUNTEDOVER as i32;
    }
}

impl std::fmt::Display for FileEvents {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut flags = Vec::new();
        if self.contains(FileEvents::ACCESS) {
            flags.push("Access");
        }
        if self.contains(FileEvents::MODIFIED) {
            flags.push("Modified");
        }
        if self.contains(FileEvents::ATTRIB) {
            flags.push("Attrib");
        }
        if self.contains(FileEvents::TRUNC) {
            flags.push("Trunc");
        }
        if self.contains(FileEvents::NOFOLLOW) {
            flags.push("NoFollow");
        }
        if self.contains(FileEvents::DELETE) {
            flags.push("Delete");
        }
        if self.contains(FileEvents::RENAME_TO) {
            flags.push("RenameTo");
        }
        if self.contains(FileEvents::RENAME_FROM) {
            flags.push("RenameFrom");
        }
        if self.contains(FileEvents::UNMOUNTED) {
            flags.push("Unmounted");
        }
        if self.contains(FileEvents::MOUNTEDOVER) {
            flags.push("MountedOver");
        }

        if flags.is_empty() {
            write!(f, "(empty)")
        } else {
            write!(f, "{}", flags.join(" | "))
        }
    }
}

/// A safe wrapper around a Solaris/illumos event port.
///
/// Event ports provide a mechanism for multiplexing events from different sources
/// including file descriptors, timers, AIO operations, and user-defined events.
///
/// The port is automatically closed when this struct is dropped.
pub struct EventPort {
    fd: RawFd,
}

impl EventPort {
    /// Creates a new event port.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The maximum number of ports is exceeded (`EAGAIN`)
    /// - The process has too many open file descriptors (`EMFILE`)
    pub fn new() -> Result<Self, PortCreateError> {
        let fd = unsafe { sys::port_create() };
        if fd < 0 {
            Err(PortCreateError(io::Error::last_os_error()))
        } else {
            Ok(EventPort { fd })
        }
    }

    /// Returns the raw file descriptor for this port.
    pub fn as_raw_fd(&self) -> RawFd {
        self.fd
    }

    /// Associates a file descriptor with the port.
    ///
    /// The file descriptor will be monitored for the specified events (same as
    /// poll(2) events). When an event occurs, it can be retrieved with `get()`
    /// or `get_n()`.
    ///
    /// Note: After an event is retrieved, the association is automatically
    /// removed and must be re-established to continue monitoring.
    ///
    /// # Arguments
    ///
    /// * `fd` - The file descriptor to monitor
    /// * `events` - Poll events to monitor (e.g., `PollEvents::IN | PollEvents::OUT`)
    /// * `user` - User-defined data returned with the event
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The port or file descriptor is invalid
    /// - The maximum number of associations is exceeded
    pub fn associate_fd(
        &self,
        fd: RawFd,
        events: PollEvents,
        user: usize,
    ) -> Result<(), AssociateFdError> {
        let ret = unsafe {
            sys::port_associate(
                self.fd,
                sys::PORT_SOURCE_FD as i32,
                fd as usize,
                events.bits(),
                user as *mut std::ffi::c_void,
            )
        };
        if ret < 0 {
            Err(AssociateFdError {
                fd,
                source: io::Error::last_os_error(),
            })
        } else {
            Ok(())
        }
    }

    /// Removes the association of a file descriptor from the port.
    ///
    /// # Arguments
    ///
    /// * `fd` - The file descriptor to dissociate
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The port is invalid
    /// - The file descriptor is not associated with the port
    pub fn dissociate_fd(&self, fd: RawFd) -> Result<(), DissociateFdError> {
        let ret = unsafe {
            sys::port_dissociate(
                self.fd,
                sys::PORT_SOURCE_FD as i32,
                fd as usize,
            )
        };
        if ret < 0 {
            Err(DissociateFdError {
                fd,
                source: io::Error::last_os_error(),
            })
        } else {
            Ok(())
        }
    }

    /// Associates a file or directory with the port for monitoring file system
    /// events.
    ///
    /// This function monitors the specified file or directory for access,
    /// modification, and attribute changes. The `file_obj` parameter contains
    /// the path and timestamps from a previous `stat()` call. At association
    /// time, these timestamps are compared with the current file state:
    ///
    /// - If `fo_atime` differs, a `FILE_ACCESS` event is generated
    /// - If `fo_mtime` differs, a `FILE_MODIFIED` event is generated
    /// - If `fo_ctime` differs, a `FILE_ATTRIB` event is generated
    ///
    /// If no changes are detected at association time, an event will be
    /// delivered when such a change occurs in the future.
    ///
    /// **Important**: After an event is retrieved with `get()` or `get_n()`,
    /// the file object is automatically dissociated. You must call
    /// `associate_file()` again to continue monitoring.
    ///
    /// **Lifetime requirement**: The `file_obj` must remain valid (not dropped
    /// or moved) until either:
    /// - An event is retrieved for this file
    /// - The file is explicitly dissociated with `dissociate_file()`
    /// - The port is closed
    ///
    /// # Arguments
    ///
    /// * `file_obj` - A `FileObj` containing the file path and timestamps. The
    ///   caller must keep this alive for the duration of the association.
    /// * `events` - Events to monitor (e.g., `FileEvents::MODIFIED | FileEvents::ATTRIB`).
    ///   Exception events (DELETE, RENAME_*, UNMOUNTED, MOUNTEDOVER) are always delivered
    ///   and cannot be filtered.
    /// * `user` - User-defined data returned with the event
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The port is invalid (`EBADF`)
    /// - Search permission is denied on a path component (`EACCES`)
    /// - The file does not exist (`ENOENT`)
    /// - The maximum number of associations is exceeded (`EAGAIN`)
    /// - The file system does not support file events (`ENOTSUP`)
    ///
    /// # Example
    ///
    /// ```no_run
    /// use event_ports_sys::{EventPort, FileObj, FileEvents};
    ///
    /// let port = EventPort::new()?;
    /// let file_obj = FileObj::new("/tmp/myfile")?;
    ///
    /// // Associate and keep file_obj alive
    /// port.associate_file(&file_obj, FileEvents::MODIFIED | FileEvents::ATTRIB, 0)?;
    ///
    /// // file_obj must stay in scope until we get the event or dissociate
    /// let event = port.get(None)?;
    ///
    /// // After getting the event, must re-associate to continue watching
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub fn associate_file(
        &self,
        file_obj: &FileObj,
        events: FileEvents,
        user: usize,
    ) -> Result<(), AssociateFileError> {
        let ret = unsafe {
            sys::port_associate(
                self.fd,
                sys::PORT_SOURCE_FILE as i32,
                file_obj.as_ptr(),
                events.bits(),
                user as *mut std::ffi::c_void,
            )
        };
        if ret < 0 {
            Err(AssociateFileError {
                path: file_obj.path().to_owned(),
                source: io::Error::last_os_error(),
            })
        } else {
            Ok(())
        }
    }

    /// Removes the association of a file object from the port.
    ///
    /// # Arguments
    ///
    /// * `file_obj` - The file object to dissociate
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The port is invalid
    /// - The file object is not associated with the port (`ENOENT`)
    /// - The caller is not the owner of the association (`EACCES`)
    pub fn dissociate_file(
        &self,
        file_obj: &FileObj,
    ) -> Result<(), DissociateFileError> {
        let ret = unsafe {
            sys::port_dissociate(
                self.fd,
                sys::PORT_SOURCE_FILE as i32,
                file_obj.as_ptr(),
            )
        };
        if ret < 0 {
            Err(DissociateFileError {
                path: file_obj.path().to_owned(),
                source: io::Error::last_os_error(),
            })
        } else {
            Ok(())
        }
    }

    /// Sends a user-defined event to the port.
    ///
    /// # Arguments
    ///
    /// * `events` - User-defined event flags
    /// * `user` - User-defined data returned with the event
    ///
    /// # Errors
    ///
    /// Returns an error if the port is invalid or the operation fails.
    pub fn send(&self, events: i32, user: usize) -> Result<(), SendError> {
        let ret = unsafe {
            sys::port_send(self.fd, events, user as *mut std::ffi::c_void)
        };
        if ret < 0 {
            Err(SendError(io::Error::last_os_error()))
        } else {
            Ok(())
        }
    }

    /// Retrieves a single event from the port.
    ///
    /// # Arguments
    ///
    /// * `timeout` - Optional timeout. `None` blocks indefinitely,
    ///   `Some(Duration::ZERO)` polls.
    ///
    /// # Returns
    ///
    /// Returns a `PortEvent` if an event is available.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The timeout expires (`ETIME`)
    /// - A signal is caught (`EINTR`)
    /// - The port is invalid
    pub fn get(
        &self,
        timeout: Option<Duration>,
    ) -> Result<PortEvent, GetError> {
        let mut event = MaybeUninit::<sys::port_event_t>::uninit();

        let timeout_ptr = if let Some(duration) = timeout {
            let mut ts = sys::timespec {
                tv_sec: duration.as_secs() as i64,
                tv_nsec: duration.subsec_nanos() as i64,
            };
            &mut ts as *mut sys::timespec
        } else {
            std::ptr::null_mut()
        };

        let ret =
            unsafe { sys::port_get(self.fd, event.as_mut_ptr(), timeout_ptr) };

        if ret < 0 {
            Err(GetError(io::Error::last_os_error()))
        } else {
            let event = unsafe { event.assume_init() };
            Ok(PortEvent::from_raw(event))
        }
    }

    /// Retrieves multiple events from the port.
    ///
    /// # Arguments
    ///
    /// * `max` - Maximum number of events to retrieve
    /// * `timeout` - Optional timeout. `None` blocks indefinitely,
    ///   `Some(Duration::ZERO)` polls.
    ///
    /// # Returns
    ///
    /// Returns a vector of `PortEvent`s. May return fewer events than `max` if
    /// the timeout expires or fewer events are available.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - A signal is caught (`EINTR`)
    /// - The port is invalid
    ///
    /// Note: `ETIME` is not an error - the function returns any events
    ///       retrieved before timeout.
    pub fn get_n(
        &self,
        max: usize,
        timeout: Option<Duration>,
    ) -> Result<Vec<PortEvent>, GetNError> {
        let mut events: Vec<MaybeUninit<sys::port_event_t>> =
            (0..max).map(|_| MaybeUninit::uninit()).collect();
        let mut nget = max as u32;

        let timeout_ptr = if let Some(duration) = timeout {
            let mut ts = sys::timespec {
                tv_sec: duration.as_secs() as i64,
                tv_nsec: duration.subsec_nanos() as i64,
            };
            &mut ts as *mut sys::timespec
        } else {
            std::ptr::null_mut()
        };

        let ret = unsafe {
            sys::port_getn(
                self.fd,
                events.as_mut_ptr() as *mut sys::port_event_t,
                max as u32,
                &mut nget,
                timeout_ptr,
            )
        };

        if ret < 0 {
            let err = io::Error::last_os_error();
            // ETIME is not really an error for port_getn - it returns partial results
            if err.raw_os_error() == Some(libc::ETIME) {
                // Return the events we got
                let result = events
                    .into_iter()
                    .take(nget as usize)
                    .map(|e| PortEvent::from_raw(unsafe { e.assume_init() }))
                    .collect();
                return Ok(result);
            }
            return Err(GetNError(err));
        }

        let result = events
            .into_iter()
            .take(nget as usize)
            .map(|e| PortEvent::from_raw(unsafe { e.assume_init() }))
            .collect();
        Ok(result)
    }
}

impl Drop for EventPort {
    fn drop(&mut self) {
        unsafe {
            libc::close(self.fd);
        }
    }
}

impl AsRawFd for EventPort {
    fn as_raw_fd(&self) -> RawFd {
        self.fd
    }
}

/// A file object for monitoring file system events with `PORT_SOURCE_FILE`.
///
/// This struct safely manages the `file_obj` structure and its associated path
/// string required for file system event monitoring. It owns both the path
/// string and ensures proper memory layout for FFI.
///
/// **Important**: A `FileObj` must remain in scope (not dropped) for the entire
/// duration of its association with a port. Dropping it while associated will
/// lead to undefined behavior as the kernel holds a pointer to the internal
/// structure.
///
/// # Example
///
/// ```no_run
/// use event_ports_sys::{EventPort, FileObj, FileEvents};
///
/// let port = EventPort::new()?;
/// let file_obj = FileObj::new("/tmp/myfile")?;
///
/// port.associate_file(&file_obj, FileEvents::MODIFIED, 0)?;
///
/// // file_obj must stay alive until event is retrieved or dissociated
/// let event = port.get(None)?;
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
pub struct FileObj {
    inner: sys::file_obj,
    _path: CString,
}

impl FileObj {
    /// Creates a new `FileObj` for the given file path.
    ///
    /// This function calls `stat()` on the path to retrieve the current
    /// timestamps (access time, modification time, and change time). These
    /// timestamps are stored in the `FileObj` and will be compared against the
    /// file's current state when associated with a port.
    ///
    /// # Arguments
    ///
    /// * `path` - UTF-8 path to the file or directory to monitor
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The path contains interior null bytes
    /// - The file does not exist or cannot be accessed
    /// - `stat()` fails for any other reason
    pub fn new<'a>(
        path: impl Into<&'a Utf8Path>,
    ) -> Result<Self, FileObjError> {
        use std::os::unix::fs::MetadataExt;

        let path = path.into();
        let path_owned = path.to_owned();

        let metadata =
            std::fs::metadata(path).map_err(|e| FileObjError::Stat {
                path: path_owned.clone(),
                source: e,
            })?;
        let cpath = CString::new(path.as_str()).map_err(|e| {
            FileObjError::InvalidPath {
                path: path_owned,
                source: e,
            }
        })?;

        let inner = sys::file_obj {
            fo_atime: sys::timespec {
                tv_sec: metadata.atime(),
                tv_nsec: metadata.atime_nsec(),
            },
            fo_mtime: sys::timespec {
                tv_sec: metadata.mtime(),
                tv_nsec: metadata.mtime_nsec(),
            },
            fo_ctime: sys::timespec {
                tv_sec: metadata.ctime(),
                tv_nsec: metadata.ctime_nsec(),
            },
            fo_pad: [0; 3],
            fo_name: cpath.as_ptr() as *mut i8,
        };

        Ok(FileObj {
            inner,
            _path: cpath,
        })
    }

    /// Creates a new `FileObj` with the `FILE_NOFOLLOW` flag.
    ///
    /// When this flag is set, symbolic links are not followed. The link itself
    /// is monitored rather than its target. Use `lstat()` semantics instead
    /// of `stat()`.
    ///
    /// # Arguments
    ///
    /// * `path` - UTF-8 path to the file, directory, or symbolic link to
    ///   monitor
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The path contains interior null bytes
    /// - The file does not exist or cannot be accessed
    /// - `lstat()` fails for any other reason
    pub fn new_nofollow(path: &Utf8Path) -> Result<Self, FileObjError> {
        use std::os::unix::fs::MetadataExt;

        let path_owned = path.to_owned();
        let metadata = std::fs::symlink_metadata(path).map_err(|e| {
            FileObjError::Stat {
                path: path_owned.clone(),
                source: e,
            }
        })?;
        let cpath = CString::new(path.as_str()).map_err(|e| {
            FileObjError::InvalidPath {
                path: path_owned,
                source: e,
            }
        })?;

        let inner = sys::file_obj {
            fo_atime: sys::timespec {
                tv_sec: metadata.atime(),
                tv_nsec: metadata.atime_nsec(),
            },
            fo_mtime: sys::timespec {
                tv_sec: metadata.mtime(),
                tv_nsec: metadata.mtime_nsec(),
            },
            fo_ctime: sys::timespec {
                tv_sec: metadata.ctime(),
                tv_nsec: metadata.ctime_nsec(),
            },
            fo_pad: [0; 3],
            fo_name: cpath.as_ptr() as *mut i8,
        };

        Ok(FileObj {
            inner,
            _path: cpath,
        })
    }

    /// Returns the pointer to the underlying `file_obj` structure for FFI.
    ///
    /// This is used internally by `EventPort::associate_file()` and should not
    /// be used directly in safe code.
    fn as_ptr(&self) -> usize {
        &self.inner as *const sys::file_obj as usize
    }

    /// Returns the path associated with this file object.
    pub fn path(&self) -> &Utf8Path {
        Utf8Path::new(self._path.to_str().unwrap())
    }

    /// Refreshes the file object with current metadata from the filesystem.
    ///
    /// This method calls `stat()` on the file path and updates the internal timestamps
    /// (fo_atime, fo_mtime, fo_ctime) to reflect the current state of the file.
    ///
    /// **Note**: This method always follows symbolic links, even if the `FileObj` was
    /// originally created with `new_nofollow()`. If you need to preserve `lstat()`
    /// semantics, create a new `FileObj` with `new_nofollow()` instead.
    ///
    /// This is particularly useful when re-associating a file after receiving an
    /// event, as it ensures the timestamps are current and will correctly detect
    /// future changes.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The file no longer exists or cannot be accessed
    /// - `stat()` fails for any other reason
    ///
    /// # Example
    ///
    /// ```no_run
    /// use event_ports_sys::{EventPort, FileObj, FileEvents};
    ///
    /// let port = EventPort::new()?;
    /// let mut file_obj = FileObj::new("/tmp/myfile")?;
    ///
    /// port.associate_file(&file_obj, FileEvents::MODIFIED, 0)?;
    /// let event = port.get(None)?;
    ///
    /// // Refresh timestamps before re-associating
    /// file_obj.refresh()?;
    /// port.associate_file(&file_obj, FileEvents::MODIFIED, 0)?;
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub fn refresh(&mut self) -> Result<(), RefreshError> {
        use std::os::unix::fs::MetadataExt;

        let path = self.path().to_owned();
        let metadata = std::fs::metadata(&path)
            .map_err(|e| RefreshError { path, source: e })?;

        self.inner.fo_atime = sys::timespec {
            tv_sec: metadata.atime(),
            tv_nsec: metadata.atime_nsec(),
        };
        self.inner.fo_mtime = sys::timespec {
            tv_sec: metadata.mtime(),
            tv_nsec: metadata.mtime_nsec(),
        };
        self.inner.fo_ctime = sys::timespec {
            tv_sec: metadata.ctime(),
            tv_nsec: metadata.ctime_nsec(),
        };

        Ok(())
    }
}

/// A port event retrieved from an event port.
///
/// This represents an event from one of the various event sources (file
/// descriptors, timers, user events, etc.).
#[derive(Debug, Clone)]
pub struct PortEvent {
    /// The events that occurred (source-specific)
    pub events: i32,
    /// The source of the event
    pub source: EventSource,
    /// The object associated with the event (interpretation depends on source)
    pub object: usize,
    /// User-defined data provided during association
    pub user: usize,
}

impl PortEvent {
    fn from_raw(event: sys::port_event_t) -> Self {
        PortEvent {
            events: event.portev_events,
            source: EventSource::from_raw(event.portev_source),
            object: event.portev_object,
            user: event.portev_user as usize,
        }
    }

    /// If this is a file descriptor event, returns the file descriptor.
    pub fn as_fd(&self) -> Option<RawFd> {
        if matches!(self.source, EventSource::Fd) {
            Some(self.object as RawFd)
        } else {
            None
        }
    }

    /// Returns the poll events for file descriptor events.
    ///
    /// Returns `None` if this is not a file descriptor event.
    pub fn poll_events(&self) -> Option<PollEvents> {
        if matches!(self.source, EventSource::Fd) {
            PollEvents::from_bits(self.events)
        } else {
            None
        }
    }

    /// Returns the file events for file system events.
    ///
    /// Returns `None` if this is not a file system event.
    pub fn file_events(&self) -> Option<FileEvents> {
        if matches!(self.source, EventSource::File) {
            FileEvents::from_bits(self.events)
        } else {
            None
        }
    }

    /// Extracts a `FileObj` from a file system event.
    ///
    /// When a `PORT_SOURCE_FILE` event is delivered, the `portev_object` field
    /// contains a pointer to the original `file_obj` structure that was associated
    /// with the port. This method safely reconstructs a `FileObj` from that pointer.
    ///
    /// The returned `FileObj` contains:
    /// - The file path from the event's `fo_name` field
    /// - The timestamps from the event (fo_atime, fo_mtime, fo_ctime)
    ///
    /// This is useful for re-associating the file after an event is received, or
    /// for accessing the file path without keeping the original `FileObj` around.
    ///
    /// # Returns
    ///
    /// - `Ok(None)` if this is not a file system event
    /// - `Ok(Some(FileObj))` if the file object was successfully extracted
    /// - `Err(_)` if the pointer is invalid or the path contains invalid UTF-8
    ///
    /// # Safety
    ///
    /// This method dereferences the `portev_object` pointer returned by the kernel.
    /// It should be safe as long as the event was obtained through the normal
    /// `port_get()` / `port_getn()` interface.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use event_ports_sys::{EventPort, FileObj, FileEvents};
    ///
    /// let port = EventPort::new()?;
    /// let file_obj = FileObj::new("/tmp/myfile")?;
    ///
    /// port.associate_file(&file_obj, FileEvents::MODIFIED, 0)?;
    /// let event = port.get(None)?;
    ///
    /// // Get the FileObj back from the event
    /// if let Some(file_obj) = event.as_file_obj()? {
    ///     println!("Event on file: {}", file_obj.path());
    ///     // Can re-associate if needed
    ///     port.associate_file(&file_obj, FileEvents::MODIFIED, 0)?;
    /// }
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub fn as_file_obj(&self) -> Result<Option<FileObj>, ExtractFileObjError> {
        if !matches!(self.source, EventSource::File) {
            return Ok(None);
        }

        unsafe {
            let fobj_ptr = self.object as *const sys::file_obj;
            if fobj_ptr.is_null() {
                return Err(ExtractFileObjError::NullPointer);
            }

            let fobj = &*fobj_ptr;

            // Create a new CString from fo_name
            let cname = CStr::from_ptr(fobj.fo_name);
            let path = CString::new(cname.to_bytes())
                .map_err(ExtractFileObjError::InvalidPath)?;

            // Create a new file_obj with the timestamps copied and pointing to our new CString
            let inner = sys::file_obj {
                fo_atime: fobj.fo_atime,
                fo_mtime: fobj.fo_mtime,
                fo_ctime: fobj.fo_ctime,
                fo_pad: fobj.fo_pad,
                fo_name: path.as_ptr() as *mut i8,
            };

            Ok(Some(FileObj { inner, _path: path }))
        }
    }
}

/// The source of a port event.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EventSource {
    /// Asynchronous I/O completion
    Aio,
    /// Timer expiration
    Timer,
    /// User-defined event
    User,
    /// File descriptor event
    Fd,
    /// Port alert
    Alert,
    /// Message queue event
    Mq,
    /// File system event
    File,
    /// Unknown source
    Unknown(u16),
}

impl EventSource {
    fn from_raw(source: u16) -> Self {
        match source as u32 {
            sys::PORT_SOURCE_AIO => EventSource::Aio,
            sys::PORT_SOURCE_TIMER => EventSource::Timer,
            sys::PORT_SOURCE_USER => EventSource::User,
            sys::PORT_SOURCE_FD => EventSource::Fd,
            sys::PORT_SOURCE_ALERT => EventSource::Alert,
            sys::PORT_SOURCE_MQ => EventSource::Mq,
            sys::PORT_SOURCE_FILE => EventSource::File,
            _ => EventSource::Unknown(source),
        }
    }
}

// Re-export commonly used constants
pub use sys::{
    PORT_SOURCE_AIO, PORT_SOURCE_ALERT, PORT_SOURCE_FD, PORT_SOURCE_FILE,
    PORT_SOURCE_MQ, PORT_SOURCE_TIMER, PORT_SOURCE_USER,
};

// Re-export file event constants
pub use sys::{
    FILE_ACCESS, FILE_ATTRIB, FILE_DELETE, FILE_EXCEPTION, FILE_MODIFIED,
    FILE_NOFOLLOW, FILE_RENAME_FROM, FILE_RENAME_TO, FILE_TRUNC, MOUNTEDOVER,
    UNMOUNTED,
};

// Re-export poll constants from libc for convenience
pub use libc::{
    POLLERR, POLLHUP, POLLIN, POLLNVAL, POLLOUT, POLLRDNORM, POLLWRNORM,
};
