es := AssociativeArray();
ds := [5,13,17,29,37,41,53,61,73,89,97,101,109,113,137,149,157,173,181,193,
       197,229,233,241,257,269,277,281,293,313,317,337,349,353,373,389,397,
       401,409,421,433,449,457,461];
e_vals := [14,15,16,28,29,30,40,41,43,52,53,60,61,60,68,78,77,86,85,103,94,
           97,114,133,116,112,133,142,120,161,126,185,143,148,175,162,153,194,
           225,175,225,216,247,174];

assert #e_vals eq #ds;
for i in [1..#ds] do
    es[ds[i]] := e_vals[i];
end for;

printf "Testing Euler number of level 1, discriminant... D=";
for d in ds do
    printf "%o ", d;
    F := QuadraticField(d);
    G := Gamma0(F, 1*Integers(F));
    assert EulerNumber(G) eq es[d];
end for;

ds := [d : d in [2..500] | IsFundamentalDiscriminant(d)];
DN_bound := 500;

printf "Testing integrality of genus for some random (disc;level;comp)...";

for _ in [1..10] do
    d := Random(ds);
    F := QuadraticField(d);
    ZF := Integers(F);
    N := Random(IdealsUpTo(Floor(DN_bound/d),F));
    cg, cg_map := NarrowClassGroup(F);
    b := Random(cg);
    B := cg_map(b);
    printf "(%o;%o;%o),", d,IdealOneLine(N),IdealOneLine(B);
    a := CoprimeNarrowRepresentative(B,N);
    assert IsTotallyPositive(a);
    assert a*B + N eq 1*Order(N);
    B := a*B;    
    G_SL := CongruenceSubgroup("SL", "Gamma0", F, N, B);
    chi := ArithmeticGenus(G_SL);
    assert IsIntegral(chi);
    G_GL := CongruenceSubgroup("GL+", "Gamma0", F, N, B);
    chi := ArithmeticGenus(G_GL);
    assert IsIntegral(chi);
end for;

// Print newline.
print "";
