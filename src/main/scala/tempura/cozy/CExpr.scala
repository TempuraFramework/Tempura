package tempura.cozy

// representation of the Cozy fragment of Clojure
enum CExpr {
  case CNil()
  case CObject(obj: AnyRef)
  case CSymbol(name: String, namespace: String)
  case CKeyword(name: String, namespace: String)
  case CSeq(args: Vector[CExpr])
  case CMap(args: Map[CExpr, CExpr])
  case CSet(args: Set[CExpr])
  case CVec(args: Array[CExpr])
  case CInt(arg: Long)
  case CString(arg: String)
  case CBool(arg: Boolean)

  override def toString: String = {
    this match {
      case CNil() => "nil (null)"
      case CSymbol(name, ns) => s"Symbol(name=${name}, namespace=${ns})"
      case CKeyword(name, ns) => s"Keyword(:${name}, namespace=${ns})"
      case CObject(obj) => s"CObject(${obj.getClass.getName}($obj))"
      case CSeq(args) => s"CSeq(${args.mkString(", ")})"
      case CVec(args) => s"CVec(${args.mkString(", ")})"
      case CMap(args) => s"CMap(${args.mkString("; ")})"
      case CSet(args) => s"CSet(${args.mkString("; ")})"
      case CInt(number) => s"CInt(${number.toString}z)"
      case CString(s) => s"CString(${s})"
      case CBool(b) => s"CBool(${b})"
    }
  }

  override def equals(obj: Any): Boolean = {
    obj match {
      case that: CExpr =>
        (this, that) match {
          case (CNil(), CNil()) => true
          case (CSymbol(name1, ns1), CSymbol(name2, ns2)) => name1 == name2 && ns1 == ns2
          case (CKeyword(name1, ns1), CKeyword(name2, ns2)) => name1 == name2 && ns1 == ns2
          case (CObject(o1), CObject(o2)) => o1 == o2
          case (CSeq(args1), CSeq(args2)) => args1 == args2
          case (CVec(args1), CVec(args2)) => args1 sameElements args2
          case (CMap(args1), CMap(args2)) => args1.iterator sameElements args2.iterator
          case (CSet(args1), CSet(args2)) => args1.iterator sameElements args2.iterator
          case (CInt(n1), CInt(n2)) => n1 == n2
          case (CString(s1), CString(s2)) => s1 == s2
          case (CBool(b1), CBool(b2)) => b1 == b2
          case _ => false
        }
      case _ => false
    }
  }

  override def hashCode(): Int = {
    this match {
      case CNil() => 0
      case CSymbol(name, ns) => name.## ^ ns.##
      case CKeyword(name, ns) => name.## ^ ns.##
      case CObject(o) => o.##
      case CSeq(args) => args.##
      case CVec(args) => args.##
      case CMap(args) => args.##
      case CSet(args) => args.##
      case CInt(args) => args.##
      case CString(arg) => arg.##
      case CBool(arg) => arg.##
    }
  }
}

