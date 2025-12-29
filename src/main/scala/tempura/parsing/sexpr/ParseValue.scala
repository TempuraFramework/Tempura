package tempura.parsing.sexpr

enum ParseValue {
  case PTerm(value: String)
  case PString(value: String)
  case PNumber(value: Int)
  case PBool(value: Boolean)

  // this composed with parsing of SEXPRs must be idempotent
  // XXX: the only problematic part is the printing of double-quotes
  // before a string value. When writing tests, need to ensure
  // we don't repeatedly double-quote a double-quoted string returned from here.
  override def toString: String =
    this match
      case PTerm(v) => v
      case PString(v) => "\"" + v + "\""
      case PNumber(v) => v.toString
      case PBool(v) => v.toString
  
}

