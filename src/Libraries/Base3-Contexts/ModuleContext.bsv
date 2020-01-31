package ModuleContext;

import ModuleContextCore::*;
import HList::*;
import Vector::*;

export ModuleContextCore::*;
export ModuleContext::*;

//typedef 4 CLOCKCONTEXTSIZE;
typedef 9 CLOCKCONTEXTSIZE;

typeclass Context#(type mc1, type c2);
   module [mc1] getContext(c2) provisos (IsModule#(mc1, a));
   module [mc1] putContext#(c2 s)(Empty) provisos (IsModule#(mc1, a));
endtypeclass

instance Context#(Module, void);
   module [Module] getContext(st1);
      return ?;
   endmodule
   module [Module] putContext#(void c)(Empty);
   endmodule
endinstance

instance Context#(ModuleContext#(st1), st1);
   module [ModuleContext#(st1)] getContext(st1);
      let c <- getCompleteContext();
      return c;
   endmodule
   module [ModuleContext#(st1)] putContext#(st1 c1)(Empty);
      putCompleteContext(c1);
   endmodule
endinstance

instance Context#(ModuleContext#(st1), st2)
   provisos (Gettable#(st1, st2));
   module [ModuleContext#(st1)] getContext(st2);
      let c <- getCompleteContext();
      return getIt(c);
   endmodule
   module [ModuleContext#(st1)] putContext#(st2 c2)(Empty);
      let c <- getCompleteContext();
      putCompleteContext(putIt(c, c2));
   endmodule
endinstance

// ---

module [mc1] applyToContext#(function c2 f(c2 c))(Empty)
   provisos (IsModule#(mc1, a), Context#(mc1, c2));

   c2 x <- getContext();
   putContext(f(x));
endmodule

module [mc1] applyToContextM#(function module#(c2) m(c2 c))(Empty)
   provisos (IsModule#(mc1, a), Context#(mc1, c2));

   c2 x <- getContext();
   c2 y <- m(x);
   putContext(y);
endmodule

// ======

typedef struct {
   Vector#(n, Clock) clks;
   Vector#(n, Reset) rsts;
		} ClockContextP#(numeric type n);

ClockContextP#(n) initClockContext = ClockContextP {
   clks: replicate(noClock), rsts: replicate(noReset) };

typedef ClockContextP#(CLOCKCONTEXTSIZE) ClockContext;
typedef Empty ClockContextIfc;
typedef ModuleContext#(HList1#(ClockContext))     ClockModule;

module mkInitialClockContextWithClocks#(Vector#(CLOCKCONTEXTSIZE, Clock) cs,
					Vector#(CLOCKCONTEXTSIZE, Reset) rs)(ClockContext);
   return ClockContextP {clks: cs, rsts: rs };
endmodule

// ======

typeclass Expose#(type c, type ifc, numeric type n)
   dependencies (c determines (ifc, n));
   module unburyContext#(c x)(ifc);
      return error("unburyContext not defined for some typeclass");
   endmodule
   module unburyContextWithClocks#(c x, ClockContextP#(n) cc)(ifc);
      (*hide*)
      let _ifc <- unburyContext(x);
      return _ifc;
   endmodule
endtypeclass

instance Expose#(HList1#(ct1), ifc1, n)
   provisos (Expose#(ct1,ifc1,n));

   module unburyContext#(HList1#(ct1) c1)(ifc1);
      (*hide_all*) ifc1 _i1 <- unburyContext(hHead(c1));
      return _i1;
   endmodule
   module unburyContextWithClocks#(HList1#(ct1) c1, ClockContextP#(n) cc)(ifc1);
      (*hide_all*) ifc1 _i1 <- unburyContextWithClocks(hHead(c1), cc);
      return _i1;
   endmodule
endinstance

instance Expose#(HCons#(c1,c2), Tuple2#(ifc1,ifc2), n)
   provisos (Expose#(c1,ifc1,n), Expose#(c2,ifc2,n));

   module unburyContext#(HCons#(c1,c2) c12)(Tuple2#(ifc1,ifc2));
      (*hide_all*) ifc1 _i1 <- unburyContext(hHead(c12));
      (*hide_all*) ifc2 _i2 <- unburyContext(hTail(c12));
      return tuple2(_i1, _i2);
   endmodule
   module unburyContextWithClocks#(HCons#(c1,c2) c12, ClockContextP#(n) cc)(Tuple2#(ifc1,ifc2));
      (*hide_all*) ifc1 _i1 <- unburyContextWithClocks(hHead(c12), cc);
      (*hide_all*) ifc2 _i2 <- unburyContextWithClocks(hTail(c12), cc);
      return tuple2(_i1, _i2);
   endmodule
endinstance

instance Expose#(ClockContextP#(n), Empty, n);
   module unburyContext#(ClockContextP#(n) x)();
   endmodule
   module unburyContextWithClocks#(ClockContextP#(n) x, ClockContextP#(m) cc)();
   endmodule
endinstance

// ====

typeclass Hide#(type mc, type ifc);
   module [mc] reburyContext#(ifc i)(Empty);
endtypeclass

instance Hide#(mc, Empty)
   provisos (IsModule#(mc, a));
   module [mc] reburyContext#(Empty i)(Empty);
   endmodule
endinstance

instance Hide#(mc, Tuple2#(ifc1,ifc2))
   provisos (IsModule#(mc, a),
	     Hide#(mc,ifc1), Hide#(mc,ifc2));

   module [mc] reburyContext#(Tuple2#(ifc1,ifc2) i12)(Empty);
      match {.x1, .x2} = i12;
      reburyContext(x1);
      reburyContext(x2);
   endmodule
endinstance

// ====

typeclass ContextRun#(type m, type c1, type ctx2)
   dependencies ((m, c1) determines ctx2);
   module [m] runWithContext #(c1 initState, ModuleContext#(ctx2, ifcType) mkI)
        (Tuple2#(c1, ifcType));
endtypeclass

typeclass ContextsRun#(type m, type c1, type ctx2)
   dependencies ((m, c1) determines ctx2);
   module [m] runWithContexts#(c1 initState, ModuleContext#(ctx2, ifcType) mkI)
	(Tuple2#(c1, ifcType));
endtypeclass

instance ContextRun#(ModuleContext#(ctx), c1, HCons#(c1,ctx));
   module [ModuleContext#(ctx)] runWithContext#(c1 initState,
					     ModuleContext#(HCons#(c1, ctx), ifcType) mkI)
      (Tuple2#(c1, ifcType));

      ctx c0 <- getContext();
      (*hide*)
      Tuple2#(HCons#(c1, ctx), ifcType) _res <-
         liftModule(runWithCompleteContext(hCons(initState, c0), mkI));
      match {.ctx_fin, .ifc} = _res;
      putContext(hTail(ctx_fin));
      return tuple2(hHead(ctx_fin), ifc);
   endmodule
endinstance

instance ContextsRun#(ModuleContext#(ctx), c1, ctx2)
   provisos (HAppend#(c1, ctx, ctx2),
	     HSplit# (ctx2, c1, ctx));
   module [ModuleContext#(ctx)] runWithContexts#(c1 initState,
						 ModuleContext#(ctx2, ifcType) mkI)
      (Tuple2#(c1, ifcType));

      ctx c0 <- getContext();
      (*hide*)
      Tuple2#(ctx2, ifcType) _res <-
          liftModule(runWithCompleteContext(hAppend(initState, c0), mkI));
      match {.c1ctx_fin, .ifc} = _res;
      Tuple2#(c1, ctx) c1ctx= hSplit(c1ctx_fin);
      match {.c1_fin, .ctx_fin} = c1ctx;
      putContext(ctx_fin);
      return tuple2(c1_fin, ifc);
   endmodule
endinstance

instance ContextRun#(Module, c1, c1);
   module [Module] runWithContext#(c1 initState,
				   ModuleContext#(c1, ifcType) mkI)
      (Tuple2#(c1, ifcType));

      (*hide*)
      Tuple2#(c1, ifcType) _res <-
         liftModule(runWithCompleteContext(initState, mkI));
      return _res;
   endmodule
endinstance


instance ContextsRun#(Module, c1, c1);
   module [Module] runWithContexts#(c1 initState,
				    ModuleContext#(c1, ifcType) mkI)
      (Tuple2#(c1, ifcType));

      (*hide*)
      Tuple2#(c1, ifcType) _res <-
          liftModule(runWithCompleteContext(initState, mkI));
      return _res;
   endmodule
endinstance


// ====

module [Module] unbury#(c1 initState,
			ModuleContext#(c1, ifcType) mkM)(Tuple2#(ifc, ifcType))
   provisos (Expose#(c1,ifc,n));

   (*hide*)
   Tuple2#(c1, ifcType) ci <- runWithCompleteContext(initState, mkM);
   match {.c, .i} = ci;
   (*hide*)
   ifc i2 <- unburyContext(c);
   return tuple2(i2, i);
endmodule

module [Module] unburyWithClocks#(c1 initState, ModuleContext#(c1, ifcType) mkM)(Tuple2#(ifc, ifcType))
   provisos (Expose#(c1,ifc,n), Context#(ModuleContext#(c1), ClockContextP#(n)),
	     Gettable#(c1, ClockContextP#(n)));

   (*hide*)
   Tuple2#(c1, ifcType) ci <- runWithCompleteContext(initState, mkM);
   match {.c, .i} = ci;
   ClockContextP#(n) cc = getIt(c);
   (*hide*)
   ifc i2 <- unburyContextWithClocks(c, cc);
   return tuple2(i2, i);
endmodule

module [c1] rebury#(Module#(Tuple2#(ifc, ifcType)) mkI)(ifcType)
   provisos (IsModule#(c1, a), Hide#(c1, ifc));
   match {.c, .i} <- liftModule(mkI);
   reburyContext(c);
   return i;
endmodule

module [c1] reburyWithClocks#(function Module#(Tuple2#(ifc, ifcType)) mkI
				 (Vector#(n, Clock) cks, Vector#(n, Reset) rs))(ifcType)
   provisos (IsModule#(c1, a), Hide#(c1, ifc), Context#(c1, ClockContextP#(n)));
   ClockContextP#(n) clks <- getContext;
   match {.c, .i} <- liftModule(mkI(clks.clks, clks.rsts));
   (*hide_all*) let rbc <- reburyContext(c);
   return i;
endmodule

endpackage
