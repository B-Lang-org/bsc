// no explicit `export lines here so as to export everything
	       
typedef  Bit#(2) Val;
		     
typedef struct {
    Val r;
    Val g;
    Val b;
} Color deriving (Eq, Bits);

function Bool colorEQ(Color c1, Color c2);
  return ((c1.r == c2.r) && (c1.g == c2.g) && (c1.b == c2.b));
endfunction: colorEQ

function Bit#(6) colorPack(Color c);
  return ({ c.r, c.g, c.b });
endfunction: colorPack

function Color makeRGB(Val rr, Val gg, Val bb);
  return (Color { r : rr, g : gg, b : bb });
endfunction: makeRGB
		  
Color cNone;
cNone = makeRGB(0, 0, 0);
		       
Color cRed;
cRed = makeRGB(3, 0, 0);
		      
Color cGreen;
cGreen = makeRGB(0, 3, 0);
			
Color cBlue;
cBlue = makeRGB(0, 0, 3);
		       
Color cYellow;
cYellow = makeRGB(3, 3, 0);
			 
Color cPurple;
cPurple = makeRGB(3, 0, 3);
			 
Color cMagenta;
cMagenta = makeRGB(0, 3, 3);
			  
Color cWhite;
cWhite = makeRGB(3, 3, 3);
			
function Color colorOr (Color c1, Color c2);
  return (Color { r : (c1.r | c2.r), 
                  g : (c1.g | c2.g), 
                  b : (c1.b | c2.b) });
endfunction: colorOr

function Color colorXOr (Color c1, Color c2);
  return (Color { r : (c1.r ^ c2.r), 
                  g : (c1.g ^ c2.g), 
                  b : (c1.b ^ c2.b) });
endfunction: colorXOr
		  
function Val getRed(Color c);
return (c.r);
endfunction: getRed
		   
function Val getGreen(Color c);
return (c.g);
endfunction: getGreen
		     
function Val getBlue(Color c);
return (c.b);
endfunction: getBlue
		    


