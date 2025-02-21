# Time Since Epoch

A Rust library providing efficient time representation and manipulation since Unix epoch, with optional sub-second precision.

The main motivation for this struct is to halve the storage size needed for storing a timestamp (16 bytes for common types) to 8 bytes.

## Features

- **Memory Efficient**: Uses 8-byte representations for timestamps
- **No sub-second Precision**: `SecondsSinceEpoch`
- **With sub-second Precision**: `TimeSinceEpoch`
- **Conversions**: Multiple conversions implemented to/from standard Rust time types and numeric formats
- **Time deltas**: Differences between timestamps are cast to `Duration`
- **Calendar Aware**: Leap years are taken into account

## Installation

Add this to your `Cargo.toml`:

```toml
[dependencies]
timesince = { git = "https://github.com/Ukko-Ylijumala/timesince-rs" }
```

## Types

### SecondsSinceEpoch

A space-efficient timestamp using `u64` for second-level precision.

```rust
// Create a timestamp for the current time
let now = SecondsSinceEpoch::new();

// Create from a specific timestamp 2009-12-31 15:20:31 UTC
let specific = SecondsSinceEpoch::new_from(1262272831u64);

// Get start of day
let today = SecondsSinceEpoch::today();
```

### TimeSinceEpoch

A high-precision timestamp using `f64` for sub-second accuracy.

```rust
// Create a high-precision current timestamp
let now = TimeSinceEpoch::new();

// Create with sub-second precision
let precise = TimeSinceEpoch::new_from(1262272831.123f64);

// Get start of current hour
let hour = TimeSinceEpoch::this_hour();
```

## Supported Conversions

Both timestamp types support conversions with:

- `std::time::SystemTime`
- `std::time::Instant`
- `u64`, `u32`, `i64`, `i32`, `f64`

Example:
```rust
// Convert from SystemTime
let system_time = SystemTime::now();
let sse: SecondsSinceEpoch = system_time.into();

// Convert to SystemTime
let back_to_system: SystemTime = sse.into();
```

## Time Operations

```rust
use std::time::Duration;

let time1 = SecondsSinceEpoch::new();
let time2 = SecondsSinceEpoch::new_from(3600u64); // 1 hour

// Addition
let sum = time1 + time2;
let with_duration = time1 + Duration::from_secs(3600);

// Subtraction
let diff = time1 - time2;
let duration_diff = time1 - Duration::from_secs(3600);

// Get elapsed time
let elapsed = time1.since();
```

## Calendar Functions

```rust
// Get year, month, day, hour, minute, second
let (year, month, day, hour, min, sec) = year_month_day_h_m_s(1262272831);

// Check days in a specific month (handles leap years)
let days = days_in_month(2024, 2); // Returns 29 (leap year)
```

## Display Formatting

Both types implement `Display` for human-readable output:

```rust
let sse = SecondsSinceEpoch::new_from(1262272831);
println!("{}", sse); // Outputs: "2009-12-31 15:20:31"

let tse = TimeSinceEpoch::new_from(1262272831.123);
println!("{}", tse); // Outputs: "2009-12-31 15:20:31.123"
```

## Technical Details

- All timestamps are UTC-based
- Negative values are converted to 0 where applicable
- Uses saturating arithmetic to prevent overflow
- Sub-second precision is maintained with TimeSinceEpoch

## Limitations

- No timezone support (UTC only)
- Year 2999 upper limit in some functions
- No date string parsing
- Some conversions (e.g., from `Instant` and `SystemTime`) are lossy

## Testing

The library includes test coverage for most things. Run tests with:

```bash
cargo test
```

## License

Copyright (c) 2024 Mikko Tanner. All rights reserved.

License: MIT OR Apache-2.0

## Contributing

Contributions are welcome! Please feel free to submit a Pull Request.

## Version History

- 0.3.0: Initial library version
    - SecondsSinceEpoch
    - TimeSinceEpoch
    - Test coverage

This library started its life as a component of a larger application, but at some point it made more sense to separate the code into its own little project and here we are.
