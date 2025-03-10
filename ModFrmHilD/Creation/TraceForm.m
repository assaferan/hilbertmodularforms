
//////////////////// Main function: Trace Form /////////////////////////

intrinsic TraceForm(Mk::ModFrmHilD : UseCache := false, Cache := AssociativeArray()) -> ModFrmHilDElt
  {Creates the trace form in the space Mk}
  M := Parent(Mk);
  Q := Rationals();
  coeffs := AssociativeArray();
  for bb in NarrowClassGroupReps(M) do
    coeffs[bb] := AssociativeArray();
    for nu->nn in RepToIdeal(M)[bb] do
      coeffs[bb][nu] := Q!Trace(Mk, nn : precomp := true, UseCache := UseCache, Cache := Cache);
    end for;
  end for;
  return HMF(Mk, coeffs);
end intrinsic;


intrinsic TraceForm(Mk::ModFrmHilD, mm::RngOrdIdl : UseCache := false, Cache := AssociativeArray()) -> ModFrmHilDElt
  {Creates the trace form in the space Mk}
  M := Parent(Mk);
  ZF := Integers(M);
  Q := Rationals();
  coeffs := AssociativeArray();
  for bb in NarrowClassGroupReps(M) do
    coeffs[bb] := AssociativeArray();
    for nu->nn in RepToIdeal(M)[bb] do
      coeffs[bb][nu] := TraceRecurse(Mk, nn, mm : UseCache := UseCache, Cache := Cache);
    end for;
  end for;
  return HMF(Mk, coeffs);
end intrinsic;

