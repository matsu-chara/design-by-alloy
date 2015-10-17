module tour/addressBook1

sig Name, Addr {}
sig Book {
  addr: Name -> lone Addr
}

pred show(b: Book) { 
  #b.addr > 1
  #Name.(b.addr) > 1
}
run show for 3 but 1 Book
