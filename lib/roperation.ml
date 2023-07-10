

(*type opCode =
| EMPTY 0
| AVAILABLE 1
| READ 2
| SHARED_BEFORE_EXCLUSIVE 3
| WRITE 4
| UPGRADE 5
| DOWNGRADE 6
| RELEASE 7*)

type rOp = { op : int; 
             r: int;
}

