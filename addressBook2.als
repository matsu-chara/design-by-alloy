module tour/addressBook2

abstract sig Target {}
sig Addr extends Target {}
abstract sig Name extends Target {}

sig Alias, Group extends Name {}
sig Book { 
  names: set Name,
  addr: names -> some Target 
} {
    no n: Name | n in n.^addr
    all a: Alias | lone a.addr
}

pred show (b: Book) { some Alias.(b.addr) }
//run show for 3 but 1 Book

pred add (b, b': Book, n: Name, t: Target) {b'.addr =  b.addr + n -> t}
pred del (b, b': Book, n: Name, t: Target) {b'.addr = b.addr - n -> t}
fun lookup (b: Book, n: Name): set Addr {n.^(b.addr) & Addr}

assert lookupYields {
  all b: Book, n: b.names | some lookup [b, n]
}
check lookupYields for 3 but 1 Book
