
enum Value { Unassigned, True, False }

struct Variable { value: Value }

enum Literal<'a> { 
	Val(&'a Variable),
	Not(&'a Variable)
}

struct Rule<'a>(Vec<Literal<'a>>); 

