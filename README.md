# event-ports-sys

Rust bindings for illumos event ports.

Event ports provide a scalable mechanism for multiplexing events from different sources:
- File descriptors (similar to epoll/kqueue)
- File system changes (file modification, deletion, etc.)
- Timers
- Asynchronous I/O completion
- User-defined events

## Platform Support

This crate is specific to illumos systems. It requires:
- `/usr/include/port.h` header file
- Event ports support in the kernel

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
event-ports-sys = { git = "https://github.com/oxidecomputer/event-ports-sys" }
```

### Monitoring File Descriptors

```rust
use event_ports_sys::{EventPort, PollEvents};
use std::os::unix::io::AsRawFd;

let port = EventPort::new()?;
let stdin_fd = std::io::stdin().as_raw_fd();

// Monitor stdin for readable data
port.associate_fd(stdin_fd, PollEvents::IN, 0)?;

// Wait for an event
let event = port.get(None)?;
if let Some(poll_events) = event.poll_events() {
    if poll_events.contains(PollEvents::IN) {
        println!("Data available on stdin!");
    }
}
# Ok::<(), Box<dyn std::error::Error>>(())
```

### Monitoring File System Changes

Here's an example that watches a file for changes:

```rust,no_run
use event_ports_sys::{EventPort, EventSource, FileEvents, FileObj};

fn watch_file(path: &str) -> Result<(), Box<dyn std::error::Error>> {
    let port = EventPort::new()?;
    let mut file_obj = FileObj::new(path)?;

    // Monitor for various types of file events
    let events = FileEvents::ACCESS
        | FileEvents::MODIFIED
        | FileEvents::ATTRIB
        | FileEvents::TRUNC;

    port.associate_file(&file_obj, events, 0)?;

    loop {
        // Wait for a file system event
        let event = port.get(None)?;

        if event.source == EventSource::File {
            // Extract the FileObj from the event to get the path
            let fo = event.as_file_obj()?;
            let path = fo.as_ref()
                .map(|fo| fo.path().as_str())
                .unwrap_or("?");

            let events_str = event.file_events()
                .map(|e| e.to_string())
                .unwrap_or_default();

            println!("{} {}", path, events_str);
        }

        // Refresh timestamps and re-associate (one-shot semantics)
        file_obj.refresh()?;
        port.associate_file(&file_obj, events, 0)?;
    }
}
```

### Retrieving Multiple Events

Use `get_n()` to retrieve multiple events efficiently:

```rust
use event_ports_sys::{EventPort, PollEvents};
use std::time::Duration;

let port = EventPort::new()?;

// ... associate multiple file descriptors ...

// Get up to 10 events with a 1 second timeout
let events = port.get_n(10, Some(Duration::from_secs(1)))?;

for event in events {
    if let Some(poll_events) = event.poll_events() {
        println!("FD {} events: {}", event.object, poll_events);
    }
}
# Ok::<(), Box<dyn std::error::Error>>(())
```

## Error Handling

Each function returns a specific error type with contextual information:

```rust
use event_ports_sys::{EventPort, AssociateFdError, PollEvents};

let port = EventPort::new()?;

match port.associate_fd(99, PollEvents::IN, 0) {
    Ok(()) => println!("Associated successfully"),
    Err(AssociateFdError { fd, source }) => {
        eprintln!("Failed to associate fd {}: {}", fd, source);
    }
}
# Ok::<(), Box<dyn std::error::Error>>(())
```

## Low-Level Access

The raw FFI bindings are available through the `sys` module:

```rust
use event_ports_sys::sys;

unsafe {
    let port_fd = sys::port_create();
    // ... use raw FFI ...
    libc::close(port_fd);
}
```

## Important Notes

### One-Shot Semantics

File descriptor and file associations are **one-shot**: after an event is retrieved with `get()` or `get_n()`, the association is automatically removed. You must re-associate to continue monitoring:

```rust,no_run
use event_ports_sys::{EventPort, FileEvents, FileObj};

let port = EventPort::new()?;
let mut file_obj = FileObj::new("/tmp/file")?;

port.associate_file(&file_obj, FileEvents::MODIFIED, 0)?;
let event = port.get(None)?;  // Association is removed after this

// Must re-associate to continue monitoring
file_obj.refresh()?;  // Update timestamps
port.associate_file(&file_obj, FileEvents::MODIFIED, 0)?;
# Ok::<(), Box<dyn std::error::Error>>(())
```

### FileObj Lifetime

When you call `associate_file()`, the kernel stores a pointer to the `FileObj`'s internal structure. This pointer remains valid only as long as the `FileObj` exists. The Rust type system cannot enforce this safety requirement because the kernel holds a raw pointer.

You must ensure the `FileObj` remains in scope until:
- An event is retrieved with `get()` or `get_n()` (which removes the association), OR
- You explicitly call `dissociate_file()`

Dropping the `FileObj` while the kernel still holds a pointer leads to undefined behavior when the event is retrieved.

## License

Licensed under the Mozilla Public License 2.0 (MPL-2.0). See LICENSE file for details.

## See Also

- [port_create(3C)](https://illumos.org/man/3C/port_create) - illumos man page
- [port_associate(3C)](https://illumos.org/man/3C/port_associate) - illumos man page
- [port_get(3C)](https://illumos.org/man/3C/port_get) - illumos man page
