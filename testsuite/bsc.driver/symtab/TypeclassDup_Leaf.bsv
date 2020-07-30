// A typeclass with a default (which is key to causing the error)
typeclass Expose#(type c, type ifc, numeric type n)
   dependencies (c determines (ifc, n));
   module unburyContext#(c x)(ifc);
      return error("unburyContext not defined for some typeclass");
   endmodule
endtypeclass

