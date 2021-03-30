interface IEmptyMethod;
    method Action m();
endinterface: IEmptyMethod

module mkEmptyMethod(IEmptyMethod);
    method m();
        action
        endaction
    endmethod
endmodule: mkEmptyMethod

