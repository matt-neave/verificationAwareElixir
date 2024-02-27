#[macro_export]
macro_rules! parse_warn {
    ($entity_type:expr, $entity_name:expr) => {
        warn!("No parse rule matching {} for {:?}.", $entity_type, $entity_name);
    };
}