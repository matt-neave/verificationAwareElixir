pub enum FormattedCondition<'a> {
    Number(i32),
    Boolean(bool),
    StringLiteral(String),
    Primitive(String),
    Not(Box<FormattedCondition<'a>>),
    BinaryOperation(&'a str, Box<FormattedCondition<'a>>, Box<FormattedCondition<'a>>),
}