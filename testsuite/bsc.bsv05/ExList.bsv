export MyList(..);

export MyListCons(..);
		
export head;
	    
export tail;
	    
export map;
	   
export filter;
	      
export append;
	      
export concat;
	      
typedef union tagged {
    void MyNil;
    MyListCons#(a) MyCons;
} MyList #(parameter type a);
			   
typedef struct {
    a hd;
    MyList#(a) tl;
} MyListCons #(parameter type a);
			       
function MyList#(a) cons(a x, MyList#(a) xs);
    return MyCons(MyListCons { hd: x, tl: xs });
endfunction: cons
		 
function Bool isNull(MyList#(a) xs);
    Bool ret;
    case (xs) matches
        tagged MyNil: ret = True;
        default: ret = False;
    endcase
    isNull = ret;
endfunction: isNull
		 
function a head(MyList#(a) xs);
    a ret;
    case (xs) matches
        tagged MyNil: ret = error("head");
        tagged MyCons .ls: ret = ls.hd;
    endcase
    return ret;
endfunction: head
		 
function MyList#(a) tail(MyList#(a) xs);
    MyList#(a) ret;
    case (xs) matches
       tagged MyNil :  ret = error("tail");
       tagged MyCons .ls :  ret = ls.tl;
    endcase
    tail = ret;
endfunction: tail
		 
function MyList#(b) map(function b f(a x1), MyList#(a) xs);
    return isNull(xs) ? MyNil : cons(f(head(xs)), map(f, tail(xs)));
endfunction: map
		
function MyList#(a) filter(function Bool p(a x1), MyList#(a) xs);
return isNull(xs) ? MyNil : p(head(xs)) ? cons(head(xs), filter(p, tail(xs))) : filter(p, tail(xs));
endfunction: filter
		   
function MyList#(a) append(MyList#(a) xs, MyList#(a) ys);
return isNull(xs) ? ys : cons(head(xs), append(tail(xs), ys));
endfunction: append
		   
function MyList#(a) concat(MyList#((MyList#(a))) xss);
return isNull(xss) ? MyNil : append(head(xss), concat(tail(xss)));
endfunction: concat
