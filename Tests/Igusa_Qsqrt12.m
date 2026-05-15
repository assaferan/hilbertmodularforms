// This should be changed once we fix HilbertModularVariety
procedure test_Igusa_Qsqrt12()
  F := QuadraticField(12);
  ZF := Integers(F);
  B := 6;
  prec := ComputePrecisionFromHilbertSeries(N, 2*B);
  M := GradedRingOfHMFs(F, prec);
  bb := NarrowClassRepresentative(M, Different(ZF)^(-1));
  R := ApproximateGradedRing(M, 1*ZF, B : IdealClassesSupport := [bb]);
  gens := R[1];
  x := AssociativeArray();
  for k in Keys(gens) do
    assert #gens[k] eq 1;
    x[k] := gens[k][1];
  end for;
  psi := AssociativeArray();
  // psi_j are the pullbacks of the Siegel-Eisenstein forms
  for j in [4,6,10,12] do
    psi[j] := AssociativeArray(['+','-']);
    psi[j]['+'], psi[j]['-'] := SiegelEisensteinPullback(M, [j,j]);
  end for;
  assert psi[4]['+'] eq 1/4*x[2]^2 + 72*x[4];
  assert psi[6]['+'] eq 1/8*x[2]^3 - 162*x[2]*x[4] - 1728*x[6];
  assert psi[4]['-']^2 eq 7200*x[2]*x[6];
  assert psi[4]['-']*psi[6]['-'] eq -7560*x[2]^2*x[6];
  psi4psi6 := AssociativeArray();
  psi4psi6['+'] := psi[4]['+']*psi[6]['+'] + psi[4]['-']*psi[6]['-'];
  psi4psi6['-'] := psi[4]['+']*psi[6]['-'] + psi[4]['-']*psi[6]['+'];
  chi10const := -43867/(2^12*3^5*5^2*7^1*53^1);
  chi10 := AssociativeArray();
  chi10['+'] := chi10const*(psi4psi6['+']-psi[10]['+']);
  chi10['-'] := chi10const*(psi4psi6['-']-psi[10]['-']);
  assert chi10['+'] eq -1/8*x[4]*x[6];
  chi12const := 131*593/(2^13*3^7*5^3*7^2*337^1);
  psi4_3 := AssociativeArray();
  psi4_3['+'] := psi[4]['+']^3 + 3*psi[4]['+']*psi[4]['-']^2;
  psi4_3['-'] := psi[4]['-']^3 + 3*psi[4]['-']*psi[4]['+']^2;
  psi6_2 := AssociativeArray();
  psi6_2['+'] := psi[6]['+']^2 + psi[6]['-']^2;
  psi6_2['-'] := 2*psi[6]['+']*psi[6]['-'];
  chi12 := AssociativeArray();
  chi12['+'] := chi12const*(3^2*7^2*psi4_3['+']+2^1*5^3*psi6_2['+']-691*psi[12]['+']);
  chi12['-'] := chi12const*(3^2*7^2*psi4_3['-']+2^1*5^3*psi6_2['-']-691*psi[12]['-']);
  assert chi12['+'] eq 1/8*x[4]^3-1/24*x[2]*x[4]*x[6]+x[6]^2;
  assert psi[4]['-']*chi10['-'] eq 15/2*x[2]*x[6]^2;
  assert psi[4]['-']*chi12['-'] eq -15/2*x[2]*x[4]^2*x[6]+5/2*x[2]^2*x[6]^2;
  return;
end procedure;

test_Igusa_Qsqrt12();
