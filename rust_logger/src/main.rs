// Order of importance
use log::trace;
use log::debug;
use log::info;
use log::warn;
use log::error;

use log::LevelFilter;

fn main() {
    // Automatically set the level.
    // Otherwise, run the program specifiying the 'RUST_LOG' level i.e.
    // `RUST_LOG=info cargo run`
    env_logger::builder().filter_level(LevelFilter::Trace).init();
    info!("Starting up...");
    trace!("This is a trace log!");
}