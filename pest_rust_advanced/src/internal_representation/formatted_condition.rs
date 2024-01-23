pub enum FormattedCondition<'a> {
    Number(i32),
    Boolean(bool),
    StringLiteral(String),
    Primitive(String),
    BinaryOperation(&'a str, Box<FormattedCondition<'a>>, Box<FormattedCondition<'a>>),
}