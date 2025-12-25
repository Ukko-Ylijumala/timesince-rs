// Copyright (c) 2024-2025 Mikko Tanner. All rights reserved.
// License: MIT OR Apache-2.0

use serde::{Deserialize, Serialize};
use std::{
    cmp::Ordering,
    fmt::{self, Display, Formatter},
    hash::{Hash, Hasher},
    ops::{Add, AddAssign, Deref, DerefMut, Sub, SubAssign},
    time::{Duration, Instant, SystemTime},
};

/// The UNIX epoch of 1970-01-01 00:00:00 UTC.
const EPOCH: SystemTime = SystemTime::UNIX_EPOCH;
const SECONDS_IN_DAY: u64 = 86400;
const SECONDS_IN_HOUR: u32 = 3600;

/// A wrapper around the current time in seconds since the UNIX epoch of
/// 1970-01-01 00:00:00 UTC.
///
/// The main motivation for this struct is to halve the storage size needed
/// for storing a time snapshot (16 bytes for common types) to 8 bytes.
/// As sub-second precision is not always needed, this is where this struct
/// comes in handy.
///
/// The implementations facilitate the following conversions between
/// `SecondsSinceEpoch` and other time-related types. The arrows indicate
/// the direction of the conversion:
/// - SSE <--> `std::time::SystemTime`
/// - SSE <--> `std::time::Instant`
/// - SSE <--> `u64`
/// - SSE <--  `u32` (u32 only reaches until 2106. big deal...)
/// - SSE <--  `i64`
/// - SSE <--  `i32` (i32 only reaches until 2038)
/// - SSE <--  `f64`
///
/// Please note that we discard sub-second precision when converting
/// from `Instant` and `SystemTime`, hence these conversions are lossy.
#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct SecondsSinceEpoch(u64);

impl SecondsSinceEpoch {
    /// Create a new instance with the current time.
    pub fn new() -> Self {
        Self(seconds_since_epoch())
    }

    /// Create a new instance with the given time in seconds.
    /// `T` can be any type that can be cast into a `u64`.
    pub fn new_from<T: Into<u64>>(secs: T) -> Self {
        Self(secs.into())
    }

    /// Get the value of this time instance. `*self` also works due to Deref.
    pub fn get(&self) -> u64 {
        self.0
    }

    /// Duration elapsed since the creation of this instance.
    pub fn since(&self) -> Duration {
        Duration::from_secs(seconds_since_epoch() - self.0)
    }

    /// Represent this time instance as a `SystemTime`.
    pub fn as_systemtime(&self) -> SystemTime {
        self.clone().into()
    }

    /// Represent this time instance as an `Instant`.
    pub fn as_instant(&self) -> Instant {
        self.clone().into()
    }

    /// A simple wrapper around `seconds_since_epoch()`.
    pub fn now() -> u64 {
        seconds_since_epoch()
    }

    /// `SecondsSinceEpoch` as of 00:00:00 today
    pub fn today() -> Self {
        let now: u64 = seconds_since_epoch();
        Self(now - (now % SECONDS_IN_DAY))
    }

    /// `SecondsSinceEpoch` at the start of the current hour.
    pub fn this_hour() -> Self {
        let now: u64 = seconds_since_epoch();
        Self(now - (now % SECONDS_IN_HOUR as u64))
    }
}

/* --------------------------------- */

impl Default for SecondsSinceEpoch {
    fn default() -> Self {
        Self::new()
    }
}

impl AsRef<u64> for SecondsSinceEpoch {
    fn as_ref(&self) -> &u64 {
        &self.0
    }
}

// impl Deref to allow read access to the inner u64 value.
impl Deref for SecondsSinceEpoch {
    type Target = u64;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

// Mutable Deref to allow write access to the inner u64 value.
impl DerefMut for SecondsSinceEpoch {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/* --------------------------------- */

impl Add for SecondsSinceEpoch {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Self(self.0.saturating_add(rhs.0))
    }
}

impl Sub for SecondsSinceEpoch {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        Self(self.0.saturating_sub(rhs.0))
    }
}

impl Add<Duration> for SecondsSinceEpoch {
    type Output = Self;

    fn add(self, rhs: Duration) -> Self {
        Self(self.0 + rhs.as_secs())
    }
}

impl Sub<Duration> for SecondsSinceEpoch {
    type Output = Self;

    fn sub(self, rhs: Duration) -> Self {
        Self(self.0.saturating_sub(rhs.as_secs()))
    }
}

impl<T: IntoDuration> Add<T> for SecondsSinceEpoch {
    type Output = Self;

    fn add(self, rhs: T) -> Self {
        Self(self.0 + rhs.into_duration().as_secs())
    }
}

impl<T: IntoDuration> Sub<T> for SecondsSinceEpoch {
    type Output = Self;

    fn sub(self, rhs: T) -> Self {
        Self(self.0.saturating_sub(rhs.into_duration().as_secs()))
    }
}

/* --------------------------------- */

impl<T> AddAssign<T> for SecondsSinceEpoch
where
    u64: From<T>,
{
    fn add_assign(&mut self, rhs: T) {
        self.0 += u64::from(rhs);
    }
}

impl<T> SubAssign<T> for SecondsSinceEpoch
where
    u64: From<T>,
{
    fn sub_assign(&mut self, rhs: T) {
        self.0 = self.0.saturating_sub(u64::from(rhs));
    }
}

/* --------------------------------- */

// Implement `From` for converting `u64` into `SecondsSinceEpoch`.
impl From<u64> for SecondsSinceEpoch {
    fn from(v: u64) -> Self {
        Self(v)
    }
}

// Implement `From` for converting `SecondsSinceEpoch` into `u64`.
impl From<SecondsSinceEpoch> for u64 {
    fn from(v: SecondsSinceEpoch) -> u64 {
        *v
    }
}

// Implement `From` for converting `u32` into `SecondsSinceEpoch`.
impl From<u32> for SecondsSinceEpoch {
    fn from(v: u32) -> Self {
        Self(v.into())
    }
}

// Implement `From` for converting `i64` into `SecondsSinceEpoch`.
// Negative values are converted to 0.
impl From<i64> for SecondsSinceEpoch {
    fn from(v: i64) -> Self {
        Self(match v {
            v if v < 0 => 0,
            v => v as u64,
        })
    }
}

// Implement `From` for converting `i32` into `SecondsSinceEpoch`.
// Negative values are converted to 0.
impl From<i32> for SecondsSinceEpoch {
    fn from(v: i32) -> Self {
        Self(match v {
            v if v < 0 => 0,
            v => v as u64,
        })
    }
}

// Implement `From` for converting `f64` into `SecondsSinceEpoch`.
// Negative values are converted to 0.
impl From<f64> for SecondsSinceEpoch {
    fn from(v: f64) -> Self {
        Self(match v {
            v if v < 0.0 => 0,
            v => v as u64,
        })
    }
}

/* --------------------------------- */

// Implement `From` for converting `SecondsSinceEpoch` into `SystemTime`.
impl From<SecondsSinceEpoch> for SystemTime {
    fn from(v: SecondsSinceEpoch) -> SystemTime {
        EPOCH + Duration::from_secs(*v)
    }
}

// Implement `From` for converting `SystemTime` into `SecondsSinceEpoch`.
// This conversion is lossy, as we lose sub-second precision.
impl From<SystemTime> for SecondsSinceEpoch {
    fn from(v: SystemTime) -> SecondsSinceEpoch {
        SecondsSinceEpoch(v.duration_since(EPOCH).unwrap().as_secs())
    }
}

/* --------------------------------- */

// Implement `From` for converting `SecondsSinceEpoch` into `Instant`.
impl From<SecondsSinceEpoch> for Instant {
    fn from(v: SecondsSinceEpoch) -> Instant {
        Instant::now() - v.since()
    }
}

// Implement `From` for converting `Instant` into `SecondsSinceEpoch`.
// This conversion is lossy, as we lose sub-second precision.
impl From<Instant> for SecondsSinceEpoch {
    fn from(v: Instant) -> SecondsSinceEpoch {
        let instant_creation: u64 = seconds_since_epoch() - v.elapsed().as_secs();
        SecondsSinceEpoch::from(instant_creation)
    }
}

/* --------------------------------- */

impl Display for SecondsSinceEpoch {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let (y, m, d, hour, min, sec) = year_month_day_h_m_s(self.0);
        write!(f, "{y}-{:02}-{:02} {:02}:{:02}:{:02}", m, d, hour, min, sec)
    }
}

/* ######################################################################### */

/// A wrapper around the current time in seconds since the UNIX epoch of
/// 1970-01-01 00:00:00 UTC.
///
/// This is a version of `SecondsSinceEpoch` with sub-second precision,
/// with the inner value being a `f64` instead of a `u64`.
#[derive(Debug, Clone, PartialOrd, Serialize, Deserialize)]
pub struct TimeSinceEpoch(f64);

impl TimeSinceEpoch {
    /// Create a new instance with the current time.
    pub fn new() -> Self {
        Self(seconds_since_epoch_f64())
    }

    /// Create a new instance with the given time in seconds.
    /// `T` can be any type that can be cast into a `f64`.
    pub fn new_from<T: Into<f64>>(secs: T) -> Self {
        Self(secs.into())
    }

    /// Get the value of this time instance. `*self` also works due to Deref.
    pub fn get(&self) -> f64 {
        self.0
    }

    /// Duration elapsed since the creation of this instance.
    pub fn since(&self) -> Duration {
        Duration::from_secs_f64(seconds_since_epoch_f64() - self.0)
    }

    /// Represent this time instance as a `SystemTime`.
    pub fn as_systemtime(&self) -> SystemTime {
        self.clone().into()
    }

    /// Represent this time instance as an `Instant`.
    pub fn as_instant(&self) -> Instant {
        self.clone().into()
    }

    /// A simple wrapper around `seconds_since_epoch_f64()`.
    pub fn now() -> f64 {
        seconds_since_epoch_f64()
    }

    /// `TimeSinceEpoch` as of 00:00:00 today
    pub fn today() -> Self {
        let now: u64 = seconds_since_epoch();
        let midnight: u64 = now - (now % SECONDS_IN_DAY);
        Self(midnight as f64)
    }

    /// `TimeSinceEpoch` at the start of the current hour.
    pub fn this_hour() -> Self {
        let now: u64 = seconds_since_epoch();
        let start_of_hour: u64 = now - (now % SECONDS_IN_HOUR as u64);
        Self(start_of_hour as f64)
    }
}

/* --------------------------------- */

impl Default for TimeSinceEpoch {
    fn default() -> Self {
        Self::new()
    }
}

impl AsRef<f64> for TimeSinceEpoch {
    fn as_ref(&self) -> &f64 {
        &self.0
    }
}

// impl Deref to allow read access to the inner f64 value.
impl Deref for TimeSinceEpoch {
    type Target = f64;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

// Mutable Deref to allow write access to the inner f64 value.
impl DerefMut for TimeSinceEpoch {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/* --------------------------------- */

impl Hash for TimeSinceEpoch {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.to_bits().hash(state);
    }
}

impl Ord for TimeSinceEpoch {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.partial_cmp(&other.0).unwrap_or(Ordering::Equal)
    }
}

impl PartialEq for TimeSinceEpoch {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for TimeSinceEpoch {}

/* --------------------------------- */

impl Add for TimeSinceEpoch {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Self(self.0 + rhs.0)
    }
}

impl Sub for TimeSinceEpoch {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        Self(match rhs.0 {
            v if self.0 <= v => 0.0,
            v => self.0 - v,
        })
    }
}

impl Add<Duration> for TimeSinceEpoch {
    type Output = Self;

    fn add(self, rhs: Duration) -> Self {
        Self(self.0 + rhs.as_secs_f64())
    }
}

impl Sub<Duration> for TimeSinceEpoch {
    type Output = Self;

    fn sub(self, rhs: Duration) -> Self {
        Self(match rhs.as_secs_f64() {
            v if self.0 <= v => 0.0,
            v => self.0 - v,
        })
    }
}

impl<T: IntoDuration> Add<T> for TimeSinceEpoch {
    type Output = Self;

    fn add(self, rhs: T) -> Self {
        Self(self.0 + rhs.into_duration().as_secs_f64())
    }
}

impl<T: IntoDuration> Sub<T> for TimeSinceEpoch {
    type Output = Self;

    fn sub(self, rhs: T) -> Self {
        Self(match rhs.into_duration().as_secs_f64() {
            v if self.0 <= v => 0.0,
            v => self.0 - v,
        })
    }
}

/* --------------------------------- */

impl<T> AddAssign<T> for TimeSinceEpoch
where
    f64: From<T>,
{
    fn add_assign(&mut self, rhs: T) {
        self.0 += f64::from(rhs);
    }
}

impl<T> SubAssign<T> for TimeSinceEpoch
where
    f64: From<T>,
{
    fn sub_assign(&mut self, rhs: T) {
        self.0 = match f64::from(rhs) {
            v if self.0 <= v => 0.0,
            v => self.0 - v,
        };
    }
}

/* --------------------------------- */

// Implement `From` for converting `f64` into `TimeSinceEpoch`.
// Negative values are converted to 0.0.
impl From<f64> for TimeSinceEpoch {
    fn from(v: f64) -> Self {
        Self(match v {
            v if v < 0.0 => 0.0,
            v => v,
        })
    }
}

// Implement `From` for converting `TimeSinceEpoch` into `f64`.
impl From<TimeSinceEpoch> for f64 {
    fn from(v: TimeSinceEpoch) -> f64 {
        *v
    }
}

// Implement `From` for converting `u32` into `TimeSinceEpoch`.
impl From<u32> for TimeSinceEpoch {
    fn from(v: u32) -> Self {
        Self(v.into())
    }
}

// Implement `From` for converting `i64` into `TimeSinceEpoch`.
// Negative values are converted to 0.0.
impl From<i64> for TimeSinceEpoch {
    fn from(v: i64) -> Self {
        Self(match v {
            v if v < 0 => 0.0,
            v => v as f64,
        })
    }
}

// Implement `From` for converting `i32` into `TimeSinceEpoch`.
// Negative values are converted to 0.0.
impl From<i32> for TimeSinceEpoch {
    fn from(v: i32) -> Self {
        Self(match v {
            v if v < 0 => 0.0,
            v => v.into(),
        })
    }
}

// Implement `From` for converting `u64` into `TimeSinceEpoch`.
impl From<u64> for TimeSinceEpoch {
    fn from(v: u64) -> Self {
        Self(v as f64)
    }
}

// Implement `From` for converting `SecondsSinceEpoch` into `TimeSinceEpoch`.
impl From<SecondsSinceEpoch> for TimeSinceEpoch {
    fn from(v: SecondsSinceEpoch) -> TimeSinceEpoch {
        TimeSinceEpoch::from(*v as f64)
    }
}

/* --------------------------------- */

// Implement `From` for converting `TimeSinceEpoch` into `SystemTime`.
impl From<TimeSinceEpoch> for SystemTime {
    fn from(v: TimeSinceEpoch) -> SystemTime {
        EPOCH + Duration::from_secs_f64(*v)
    }
}

// Implement `From` for converting `SystemTime` into `TimeSinceEpoch`.
impl From<SystemTime> for TimeSinceEpoch {
    fn from(v: SystemTime) -> TimeSinceEpoch {
        TimeSinceEpoch(v.duration_since(EPOCH).unwrap().as_secs_f64())
    }
}

/* --------------------------------- */

// Implement `From` for converting `TimeSinceEpoch` into `Instant`.
impl From<TimeSinceEpoch> for Instant {
    fn from(v: TimeSinceEpoch) -> Instant {
        Instant::now() - v.since()
    }
}

// Implement `From` for converting `Instant` into `TimeSinceEpoch`.
impl From<Instant> for TimeSinceEpoch {
    fn from(v: Instant) -> TimeSinceEpoch {
        TimeSinceEpoch::from(seconds_since_epoch_f64() - v.elapsed().as_secs_f64())
    }
}

/* --------------------------------- */

impl Display for TimeSinceEpoch {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let (y, m, d, hour, min, sec) = year_month_day_h_m_s(self.0 as u64);
        let fract: u32 = (self.0.fract() * 1_000.001) as u32; // 0.001 to round up
        write!(f, "{y}-{:02}-{:02} {:02}:{:02}:{:02}.{:03}", m, d, hour, min, sec, fract)
    }
}

/* ######################################################################### */

/// A trait for converting types into `Duration`.
trait IntoDuration {
    fn into_duration(self) -> Duration;
}

impl IntoDuration for u64 {
    fn into_duration(self) -> Duration {
        Duration::from_secs(self)
    }
}

impl IntoDuration for u32 {
    fn into_duration(self) -> Duration {
        Duration::from_secs(self.into())
    }
}

impl IntoDuration for i64 {
    fn into_duration(self) -> Duration {
        Duration::from_secs(match self {
            v if v < 0 => 0,
            v => v as u64,
        })
    }
}

impl IntoDuration for i32 {
    fn into_duration(self) -> Duration {
        Duration::from_secs(match self {
            v if v < 0 => 0,
            v => v as u64,
        })
    }
}

impl IntoDuration for f64 {
    fn into_duration(self) -> Duration {
        Duration::from_secs_f64(match self {
            v if v < 0.0 => 0.0,
            v => v,
        })
    }
}

impl IntoDuration for f32 {
    fn into_duration(self) -> Duration {
        Duration::from_secs_f32(match self {
            v if v < 0.0 => 0.0,
            v => v,
        })
    }
}

/* ######################################################################### */

/// Return the `Duration` since the UNIX epoch.
#[inline]
pub fn time_since_epoch() -> Duration {
    SystemTime::now().duration_since(EPOCH).unwrap()
}

/// Return the current time in seconds since the UNIX epoch.
#[inline]
fn seconds_since_epoch() -> u64 {
    time_since_epoch().as_secs()
}

/// Return the current time in seconds since the UNIX epoch with sub-second precision.
#[inline]
fn seconds_since_epoch_f64() -> f64 {
    time_since_epoch().as_secs_f64()
}

/* ######################################################################### */

/// Get the year, month, day, hour, minute and second from seconds since
/// UNIX epoch. Takes leap years into account.
pub fn year_month_day_h_m_s(seconds: u64) -> (u32, u32, u32, u32, u32, u32) {
    let days: u32 = (seconds / SECONDS_IN_DAY) as u32;
    let leftover: u32 = (seconds % SECONDS_IN_DAY) as u32;
    let hour: u32 = leftover / SECONDS_IN_HOUR;
    let minute: u32 = (leftover % SECONDS_IN_HOUR) / 60;

    let mut year: u32 = 1970;
    let mut days_left: u32 = days;
    loop {
        let days_in_year: u32 = if is_leap_year(year) { 366 } else { 365 };
        if days_left < days_in_year {
            break;
        }
        days_left -= days_in_year;
        year += 1;
    }

    let mut month: u32 = 1;
    let mut days_in_month: u32 = 31;
    loop {
        if days_left < days_in_month {
            break;
        }
        days_left -= days_in_month;
        month += 1;
        update_days_in_month(&mut days_in_month, month, year);
    }

    (year, month, days_left + 1, hour, minute, leftover % 60)
}

#[inline]
fn update_days_in_month(days: &mut u32, month: u32, year: u32) {
    *days = days_in_month(year, month);
}

/// Check if a given year is a leap year.
#[inline]
fn is_leap_year(year: u32) -> bool {
    if year % 4 == 0 {
        if year % 100 == 0 {
            return year % 400 == 0;
        } else {
            return true;
        }
    } else {
        return false;
    };
}

/// Get the number of days in a month, taking leap years into account.
#[inline]
pub fn days_in_month(year: u32, month: u32) -> u32 {
    match month {
        2 => {
            if is_leap_year(year) {
                29
            } else {
                28
            }
        }
        4 | 6 | 9 | 11 => 30,
        _ => 31,
    }
}

/* ######################################################################### */

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{Duration, SystemTime};

    /// 2009-12-31 15:20:31 UTC
    const TEST_TIME: u64 = 1_262_272_831;

    #[test]
    fn test_new() {
        let new: SecondsSinceEpoch = SecondsSinceEpoch::new();
        let current_time: u64 = seconds_since_epoch();
        assert_eq!(new.get(), current_time);
    }

    #[test]
    fn test_new_from() {
        let seconds: u32 = TEST_TIME as u32;
        let sse_from: SecondsSinceEpoch = SecondsSinceEpoch::new_from(seconds);
        assert_eq!(sse_from.get(), seconds.into());
    }

    #[test]
    fn test_since() {
        let past_sse: SecondsSinceEpoch = SecondsSinceEpoch::new_from(TEST_TIME);
        let elapsed: Duration = past_sse.since();
        let now: SystemTime = SystemTime::now();
        let expected_elapsed: Duration =
            Duration::from_secs(now.duration_since(EPOCH).unwrap().as_secs())
                - Duration::from_secs(TEST_TIME);
        assert_eq!(elapsed, expected_elapsed);
    }

    #[test]
    fn test_as_systemtime() {
        let sse: SecondsSinceEpoch = SecondsSinceEpoch::new_from(TEST_TIME);
        let system_time: SystemTime = sse.into();
        let expected: SystemTime = EPOCH + Duration::from_secs(TEST_TIME);
        assert_eq!(system_time, expected);
    }

    #[test]
    fn test_as_instant() {
        let sse: SecondsSinceEpoch = SecondsSinceEpoch::new_from(TEST_TIME);
        let sse_to_instant: Instant = sse.into();
        let expected: Instant =
            Instant::now() - Duration::from_secs(seconds_since_epoch() - TEST_TIME);
        assert_eq!(sse_to_instant.elapsed().as_secs(), expected.elapsed().as_secs());
    }

    #[test]
    fn test_now() {
        let now: u64 = SecondsSinceEpoch::now();
        let current_time: u64 = seconds_since_epoch();
        assert_eq!(now, current_time);
    }

    #[test]
    fn test_add_u32() {
        let sse: SecondsSinceEpoch = SecondsSinceEpoch::new_from(TEST_TIME as u32);
        let new_time: SecondsSinceEpoch = sse + SECONDS_IN_HOUR;
        assert_eq!(*new_time, TEST_TIME + SECONDS_IN_HOUR as u64);
    }

    #[test]
    fn test_sub_u32() {
        let sse: SecondsSinceEpoch = SecondsSinceEpoch::new_from(TEST_TIME as u32);
        let new_time: SecondsSinceEpoch = sse - SECONDS_IN_HOUR;
        assert_eq!(*new_time, TEST_TIME - SECONDS_IN_HOUR as u64);
    }

    #[test]
    fn test_add_duration() {
        let sse: SecondsSinceEpoch = SecondsSinceEpoch::new_from(TEST_TIME);
        let new_time: SecondsSinceEpoch = sse + Duration::from_secs(SECONDS_IN_DAY);
        assert_eq!(*new_time, TEST_TIME + SECONDS_IN_DAY);
    }

    #[test]
    fn test_sub_duration() {
        let sse: SecondsSinceEpoch = SecondsSinceEpoch::new_from(TEST_TIME);
        let new_time: SecondsSinceEpoch = sse - Duration::from_secs(SECONDS_IN_DAY);
        assert_eq!(*new_time, TEST_TIME - SECONDS_IN_DAY);
    }

    #[test]
    fn test_add_assign_u16() {
        let mut sse: SecondsSinceEpoch = SecondsSinceEpoch::new_from(TEST_TIME);
        sse += SECONDS_IN_HOUR as u16;
        assert_eq!(*sse, TEST_TIME + SECONDS_IN_HOUR as u64);
    }

    #[test]
    fn test_sub_assign_u32() {
        let mut sse: SecondsSinceEpoch = SecondsSinceEpoch::new_from(TEST_TIME);
        sse -= SECONDS_IN_DAY as u32;
        assert_eq!(*sse, TEST_TIME - SECONDS_IN_DAY);
    }

    #[test]
    fn test_sse_today() {
        let today: SecondsSinceEpoch = SecondsSinceEpoch::today();
        let now: u64 = seconds_since_epoch();
        let (_, _, _, h, m, s) = year_month_day_h_m_s(now);
        let expected: u64 = now - (h * SECONDS_IN_HOUR + m * 60 + s) as u64;
        assert_eq!(
            *today,
            expected,
            "Today mismatch: {} != {}",
            today,
            SecondsSinceEpoch::from(expected)
        );
    }

    #[test]
    fn test_sse_this_hour() {
        let hour: SecondsSinceEpoch = SecondsSinceEpoch::this_hour();
        let now: u64 = seconds_since_epoch();
        let (_, _, _, _, m, s) = year_month_day_h_m_s(now);
        let expected: u64 = now - (m * 60 + s) as u64;
        assert_eq!(
            *hour,
            expected,
            "This hour mismatch: {} != {}",
            hour,
            SecondsSinceEpoch::from(expected)
        );
    }

    #[test]
    fn test_sse_display() {
        let sse: SecondsSinceEpoch = SecondsSinceEpoch::new_from(TEST_TIME);
        let formatted: String = format!("{}", sse);
        assert_eq!(formatted, "2009-12-31 15:20:31");
    }

    #[test]
    fn test_tse_display() {
        let mut tse: TimeSinceEpoch = TimeSinceEpoch::new_from(TEST_TIME as f64);
        tse += 0.123;
        let formatted: String = format!("{}", tse);
        assert_eq!(formatted, "2009-12-31 15:20:31.123");
        tse += 0.4567; // 0.5797
        let formatted: String = format!("{}", tse);
        assert_eq!(formatted, "2009-12-31 15:20:31.579");
        tse += 0.4197; // 0.9994
        let formatted: String = format!("{}", tse);
        assert_eq!(formatted, "2009-12-31 15:20:31.999");
        tse -= 0.998; // 0.0014
        let formatted: String = format!("{}", tse);
        assert_eq!(formatted, "2009-12-31 15:20:31.001");
    }

    #[test]
    fn test_year_month_day_h_m_s() {
        let (year, month, day, hour, minute, second) = year_month_day_h_m_s(TEST_TIME);
        assert_eq!(year, 2009, "Year mismatch");
        assert_eq!(month, 12, "Month mismatch");
        assert_eq!(day, 31, "Day mismatch");
        assert_eq!(hour, 15, "Hour mismatch");
        assert_eq!(minute, 20, "Minute mismatch");
        assert_eq!(second, 31, "Second mismatch");
        // 2999-12-31 23:59:59 UTC
        let future: u64 = 32_503_679_999;
        let (year, month, day, hour, minute, second) = year_month_day_h_m_s(future);
        assert_eq!(year, 2999, "Year mismatch (2999-12-31)");
        assert_eq!(month, 12, "Month mismatch (2999-12-31)");
        assert_eq!(day, 31, "Day mismatch (2999-12-31)");
        assert_eq!(hour, 23, "Hour mismatch (2999-12-31)");
        assert_eq!(minute, 59, "Minute mismatch (2999-12-31)");
        assert_eq!(second, 59, "Second mismatch (2999-12-31)");
    }

    /// Test `days_in_month()` against a known set of values.
    #[test]
    fn test_days_in_month() {
        let data = [
            (1604, 2, 29),
            (1632, 2, 29),
            (1776, 2, 29),
            (1970, 1, 31),
            (1970, 2, 28),
            (1970, 3, 31),
            (1970, 4, 30),
            (1970, 5, 31),
            (1970, 6, 30),
            (1970, 7, 31),
            (1970, 8, 31),
            (1970, 9, 30),
            (1970, 10, 31),
            (1970, 11, 30),
            (1970, 12, 31),
            (1972, 2, 29),
            (2015, 2, 28),
            (2016, 2, 29),
            (2019, 2, 28),
            (2020, 2, 29),
            (2023, 2, 28),
            (2024, 2, 29),
            (2027, 2, 28),
            (2028, 2, 29),
            (2348, 2, 29),
            (2404, 2, 29),
        ];

        for (year, month, expected) in data.iter() {
            #[rustfmt::skip]
            assert_eq!(days_in_month(*year, *month), *expected, "Mismatch for {}-{:02}", year, month);
        }
    }
}
