procedure test()
    _<x> := PolynomialRing(Rationals());
    F := NumberField(x^3 - x^2 - 5*x + 4);
    prec := 40;
    M := GradedRingOfHMFs(F, prec);
    M4 := HMFSpace(M, [4,4,4]);
    B4 := Basis(M4 : ViaTraceForm);
    return;
end procedure;