module tour/addressBook1

sig Name, Addr {}
sig Book {
  addr: Name -> lone Addr
}

pred show(b: Book) { 
  #b.addr > 1
  #Name.(b.addr) > 1
}

pred add(b, b': Book, n: Name, a: Addr) {
  b'.addr = b.addr + n -> a
}

pred showAdd(b, b': Book, n: Name, a: Addr) {
  add [b, b', n, a]
  #Name.(b'.addr) > 1
}

pred del(b, b': Book, n: Name) {
  b'.addr = b.addr - n -> Addr
}

fun lookup (b: Book, n: Name) : set Addr {
  n.(b.addr)
}

assert delUndoesAdd {
  all b,b', b'': Book, n: Name, a: Addr |
    no n.(b.addr) and add [b, b', n, a] and del [b', b'', n]
      implies b.addr = b''.addr
}
check delUndoesAdd for 10 but 3 Book

assert addIdempotent {
  all b, b', b'': Book, n: Name, a: Addr |
    add [b, b', n, a] and add [b', b'', n, a]
      implies b'.addr = b''.addr
}
check addIdempotent for 3

assert addLocal {
  all b, b': Book, n, n': Name, a: Addr |
    add [b, b', n, a] and n != n'
      implies lookup [b, n] = lookup [b', n]
}
check addLocal for 3 but 2 Book
