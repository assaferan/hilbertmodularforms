
/////////////// ModFrmHilD: Trace Precomputation ////////////////


/*
This file contains the following routines used for the Trace.m code:
  - HMFTracePrecomputation: A procedure that does the precomputations for the trace code (stores class number, unit index, and discriminants of rings of integers)
  - PrecomputeTraceForm: Does precomputations the trace form t
  - PrecomputeTraceForm: Does precomputations for a series of trace forms T(a_1)t, ..., T(a_n)t specified by a list of ideals [a_1,...,a_n]
  - LocalSquare: Stores values of local squares - in order to ensure that we don't repeat computations. (This can be removed if we)
*/

import "../SaveAndLoad.m": default_dir;


function TriplesFilename(ZF)
  F := NumberField(ZF);
  F_label := Join([IntegerToString(Integers()!a) : a in DefiningPolyCoeffs(F)], ".");
  return default_dir() cat F_label cat "_triples";
end function;

procedure SaveTriples(triples)
  ZF := Universe(triples);
  filename := TriplesFilename(ZF);
  WriteObject(Open(filename, "w"), [<Eltseq(k), v[1], v[2], Eltseq(v[3])> : k->v in triples]);
end procedure;

function LoadTriples(ZF)
  filename := TriplesFilename(ZF);
  b, loadfile := OpenTest(filename, "r");
  B := AssociativeArray();
  if b then
    for elt in ReadObject(loadfile) do
      B[ZF!elt[1]] := <elt[2], elt[3], ideal<ZF|[ZF!x : x in elt[4]]>>;
    end for;
  end if;
  return B;
end function;


///////////////////////////////////////////////////
//                                               //
//      Precomputation: Class Number h,          //
//      Unit Indices w, and Discriminant DD.     //
//                                               //
///////////////////////////////////////////////////


/*
The function below computes and stores the items for the trace formula. Given a CM-extension K / F we store:
  - h = ClassNumber of K
  - w = Unit Indices of K/F. Remark: Since K/F is a CM-extension then by Dirichlets unit theorem the rank of ZK^* and ZF^* are the same.
        Hence it makes to consider the quantity [ ZK^* : ZF^* ] which can be explained by
  - DD = the discriminant of ZK
This proceedure is done in the following steps:
  Given the discriminant of an order D in CM-extension K = F( sqrt(D) ) over F, we do the following:

    - Pass 1: Given an ideal aa, we compute list of elements representing all of the orders O whose class number we need
              To compute Tr T(aa). These orders are represented by a single totally negative element D such that O = ZF[ sqrt(D) ].

    - Pass 2: We run a discriminant hash which computes a unique representative d for each discriminant D up to:
              (a) the squareclass of D in F* / F*^2
              (b) the action of automorphisms s : F -> F on D.

      This gives a ** minimal ** set of discriminants for which we need to compute the class numbers and unit indices

    - Pass 3: We compute h, w, DD as above for the minimal set of discriminants. These are stored to M`ClassNumbersPrecomputation with d0 -> [h, w, DD]
    - Pass 4: We remove bad discriminants D which don't satisfy a condition on their conductor (only for Cl(F) > 1). The rest are stored to M`PrecomputationforTrace as aa -> [ [D, d0], ... ]

  Once this is complete, we can the access all of the information for a discriminant D using the hash key d0 in the associative array ClassNumbersPrecomputation
*/

// FIXME: HMFTracePrecomputation - Pass tracebasis to IdealCMextensions instead of computing each time
intrinsic HMFTracePrecomputation(M::ModFrmHilDGRng, L::SeqEnum[RngOrdIdl] : SaveAndLoad:=true, UseCache := false, Cache := AssociativeArray())
  {Precomputes class number and unit indices for a list of ideals L}

  // Do nothing if L is empty
  if #L eq 0 then
    return;
  end if;

  // initialize
  F := BaseField(M); // Base Field
  ZF := Integers(F); // Ring of Integers
  _<x> := PolynomialRing(F); // Polynomial ring over F
  UF := UnitGroup(M); // Unit Group of F
  mUF := UnitGroupMap(M); // Unit Group of F map
  C,mC := ClassGroup(F); // class group
  Creps := [ mC(i) : i in C ]; // class group representatives
  NCreps := NarrowClassGroupReps(M); // narrow class group representatives
  SetClassGroupBounds("GRH"); // Bounds

  // Assign automorphism to GradedRing (used in DiscriminantHash)
  if not assigned M`Automorphisms then
    M`Automorphisms := Automorphisms(F);
  end if;

  /////////// Hash function //////////
  // For each discriminant d, this hash function associates a unique element w in F representing the field F(x)/(x^2-d) up to isomorphism over QQ. It runs in two phases:
  //
  // *  Phase 1: Pick a unique representative for the square class of [d] in F*/F*2. Write the discriminant as d * ZF = mm * aa^2 with mm squarefree. Fix a set of representatives for the class group,
  //             and let [ bb ] = [ aa ] be the ideal representing the class of aa in CL(F). Then [aa * bb^(-1)] = (x) for some x in ZF so d * ZF = mm * bb^2 * (x)^2. Let d0 := d / x^2.
  //             Thus a unique representative for the square class of d can be picked as the "reduced fundamental domain rep generator" for -d0 with respect the square of the fundamental unit.
  //
  // *  Phase 2: Pick a unique representative for the square class of [d] up to Aut(F). If s : F -> F is a nontrivial automorphism, then fields F[x]/(x^2 - d) and F/(x^2 - s(d)) are isomorphic over QQ.
  //             We pick a unique representative d' among the conjugates of d by sorting the conjugates lexicographically according to their embeddings at a fixed set of real places. For this step,
  //             we store the automorphism group of F to the GradedRingofHMFS and then record the index c such that the automorphism f = Aut[c] satifies f(d') = d.
  //
  ///////////////////////////////////

  // This needs to be updated for general fields
  function DiscriminantHash(D : UseCache := false, Cache := AssociativeArray())
    // Phase 1
    mm := D * ZF;
    aa := &*( [1*ZF] cat [ pp[1] ^ (pp[2] div 2) : pp in Factorization(mm)] ); // Note pp[2] div 2 = Floor(pp[2]/2)
    for bb in Creps do
      boo, x := IsPrincipal( aa * bb^(-1) );
      if boo then
        elt := FunDomainRep(M, -D / x^2 : Squares := true);
        d := ZF ! -elt;
        break;
      end if;
    end for;
    // assert IsSquare(D/d); // can be dropped

    // Phase 2
    // Sort conjugates lexicographically by size of embedding
    A := [ i : i in M`Automorphisms ];
    embs := [ RealEmbeddings(f(d)) : f in A ];
    ParallelSort(~embs, ~A);

    // select unique conjugate + index c such that f = M'Aut[c] satisfies f(d0) = d
    f  := A[1];
    d0 := ZF ! f(d);
    c  := Index( M`Automorphisms, f^(-1) );

    // return
    return d0, c;
  end function;


  // Precomputations
  A := TracePrecomputation(M);
  B := ClassNumbersPrecomputation(M);

  if SaveAndLoad then
    for k->v in LoadTriples(ZF) do
      B[k] := v;
    end for;
  end if;

  // First pass. A[mm][aa] := List of [b,a,D]
  vprintf HilbertModularForms, 1 : "start %o. \n", Cputime();

  Discs := {};
  ideals := Set(L) diff Keys(A); // ideals to precompute
  for mm in ideals do
    A[mm] := AssociativeArray();
    for aa in Creps do
      A[mm][aa] := [];
      if IsNarrowlyPrincipal(mm * aa^2) then
        Points := IndexOfSummation(M, mm, aa : precomp := true);
        for i in Points do
          b := i[1]; // Trace
          a := i[2]; // Norm
          D := b^2-4*a; // Discriminant
          A[mm][aa] cat:= [[b,a,D]];
          Include(~Discs, D);
        end for;
      end if;
    end for;
  end for;


  // Second pass. Compute a hash with unique discriminants up to squares.
  vprintf HilbertModularForms, 1 : "Pass 1 finished at %o. Now computing reduced discriminants for %o orders. \n", Cputime(), #Discs;

  Hash := AssociativeArray();
  RDiscs := {};
  for D in Discs do
    d, c := DiscriminantHash(D : UseCache := UseCache, Cache := Cache);
    Include(~RDiscs, d);
    Hash[D] := [d, c];
  end for;

  /*
  RDiscs := [ZF |
    [1, -3, -2],
    [2, -3, -2],
    [-7, -10, -7],
    [-55, 60, -16],
    [-43, 8, 4],
    [1, 0, -8],
    [49, -42, -31],
    [1, -10, -7],
    [5, -10, -7],
    [13, -34, -19],
    [-14, -6, -1],
    [-10, -6, -1],
    [-7, 4, -2],
    [-51, -1, 9],
    [-39, 50, -15],
    [-6, -9, -3],
    [-123, 1, 20],
    [25, -24, -20],
    [-35, 50, -15],
    [-71, 6, 9],
    [-79, 58, -11],
    [41, -48, -32],
    [-7, -16, -8],
    [-67, 6, 9],
    [-17, 11, -2],
    [1, -16, -8],
    [-59, -7, 8],
    [-11, -2, -3],
    [-51, -31, -4],
    [-91, -23, 8],
    [-30, 2, 3],
    [-7, -2, -3],
    [-26, 2, 3],
    [-3, -2, -3],
    [-23, 2, 3],
    [29, -27, -19],
    [1, -2, -3],
    [2, -2, -3],
    [9, -26, -15],
    [17, -50, -27],
    [-42, 9, 3],
    [-18, 15, -4],
    [-14, 15, -4],
    [-63, 0, 8],
    [-79, 1, 12],
    [-55, 0, 8],
    [-31, 6, 1],
    [10, -9, -8],
    [-75, 1, 12],
    [39, -37, -26],
    [-27, 6, 1],
    [13, -12, -10],
    [-7, -8, -4],
    [14, -12, -10],
    [1, -32, -16],
    [-23, 6, 1],
    [-47, 0, 8],
    [-95, 8, 12],
    [-51, 29, -4],
    [-35, -24, -4],
    [1, -8, -4],
    [-19, -4, 2],
    [-59, 81, -24],
    [-131, 16, 16],
    [1, -18, -11],
    [-83, -2, 13],
    [-79, -2, 13],
    [6, -15, -9],
    [-39, 42, -11],
    [-35, -10, 1],
    [-31, 0, 0],
    [-75, -2, 13],
    [-31, -10, 1],
    [-29, 26, -6],
    [-25, 3, 2],
    [-2, -1, -4],
    [-23, 0, 0],
    [-21, 3, 2],
    [-19, 3, 2],
    [-19, 0, 0],
    [-15, 0, 0],
    [-17, 16, -5],
    [-11, 0, 0],
    [18, -25, -16],
    [-13, 16, -5],
    [-6, 0, 0],
    [1, -21, -10],
    [-5, 0, 0],
    [-3, 0, 0],
    [-2, 0, 0],
    [-1, 0, 0],
    [-79, -8, 12],
    [-53, 24, -1],
    [-70, 2, 11],
    [-22, 7, 0],
    [-19, 7, 0],
    [2, -7, -5],
    [6, -7, -5],
    [7, -7, -5],
    [-35, -2, 5],
    [-31, -2, 5],
    [-63, 44, -8],
    [-95, 0, 16],
    [14, -17, -12],
    [18, -17, -12],
    [-22, -9, 0],
    [-1, -13, -6],
    [-47, 34, -7],
    [-39, -8, 4],
    [-6, 1, -1],
    [-5, 1, -1],
    [-2, 1, -1],
    [-1, 1, -1],
    [-119, -2, 21],
    [10, -23, -13],
    [-65, 3, 10],
    [-17, 8, -1],
    [-159, 6, 25],
    [-15, 8, -1],
    [3, -6, -6],
    [-14, 8, -1],
    [-19, 21, -8],
    [-42, 38, -9],
    [7, -6, -6],
    [-57, 16, 3],
    [-30, -1, 4],
    [-9, -5, -2],
    [-27, -1, 4],
    [-5, -5, -2],
    [-3, -5, -2],
    [-23, -1, 4],
    [-119, -8, 20],
    [-139, -7, 24],
    [-90, 1, 15],
    [29, -27, -24],
    [-15, 12, -3],
    [93, -83, -60],
    [-9, 2, -2],
    [-7, 2, -2],
    [-67, 65, -16],
    [-5, 2, -2],
    [-3, 2, -2],
    [-143, 0, 24],
    [-139, 0, 24],
    [-51, 26, -3],
    [-47, 26, -3],
    [-37, 10, 2],
    [-11, 9, -2],
    [21, -19, -20],
    [-29, 0, 3],
    [-25, 0, 3],
    [-46, 1, 7],
    [-23, 0, 3],
    [113, -100, -72],
    [-21, 0, 3],
    [27, -32, -21],
    [1, -4, -3],
    [-19, 0, 3],
    [-23, 13, -4],
    [3, -4, -3],
    [-18, 0, 3],
    [-19, 13, -4],
    [-22, 29, -9],
    [-15, 13, -4],
    [49, -43, -32],
    [-10, 13, -4],
    [11, -14, -10],
    [-31, 20, -4],
    [15, -14, -10],
    [-27, 20, -4],
    [13, -11, -16],
    [-11, -3, -4],
    [-55, 18, 1],
    [69, -60, -44],
    [-7, -3, -4],
    [-63, 70, -19],
    [-51, 18, 1],
    [-3, -3, -4],
    [-45, 2, 6],
    [1, -3, -4],
    [-41, 2, 6],
    [57, -59, -40],
    [-99, 145, -44],
    [13, -27, -16],
    [-41, 31, -6],
    [-14, 14, -5],
    [-7, -2, 0],
    [-6, -2, 0],
    [-5, -2, 0],
    [81, -70, -51],
    [-27, 5, 0],
    [-23, 5, 0],
    [-65, 0, 11],
    [-23, 18, -7],
    [3, -9, -5],
    [-15, 5, 0],
    [-15, 18, -7],
    [-59, 13, 4],
    [-35, 12, 0],
    [-55, 13, 4],
    [-31, 12, 0],
    [5, -19, -12],
    [9, -19, -12],
    [17, -43, -24],
    [-31, -11, 0],
    [13, -19, -12],
    [-27, -11, 0],
    [-75, 49, -8],
    [33, -30, -23],
    [45, -54, -35],
    [5, -12, -12],
    [-3, -1, -1],
    [-2, -1, -1],
    [-1, -1, -1],
    [9, -12, -12],
    [-147, 13, 20],
    [1, -1, -1],
    [13, -12, -12],
    [73, -68, -48],
    [25, -36, -24],
    [-45, 23, -2],
    [-43, -3, 4],
    [1, -11, -8],
    [37, -60, -36],
    [-14, 6, -1],
    [5, -11, -8],
    [33, -36, -24],
    [-11, 6, -1],
    [-35, -3, 4],
    [-10, 6, -1],
    [9, -11, -8],
    [-37, 36, -9],
    [-31, -3, 4],
    [17, -35, -20],
    [-23, -27, -8],
    [-7, -7, -2],
    [25, -22, -19],
    [-27, 10, -3],
    [-7, -4, -8],
    [41, -46, -31],
    [18, -18, -13],
    [1, -4, -8],
    [-15, 10, -3],
    [-19, 26, -8],
    [-59, 5, 8],
    [5, -4, -8],
    [-47, 56, -16],
    [-11, 10, -3],
    [5, -17, -9],
    [-7, 10, -3],
    [-79, 12, 8],
    [21, -28, -20],
    [-87, 64, -12],
    [-35, 46, -15],
    [29, -28, -20],
    [-19, 1, 2],
    [-15, 1, 2],
    [-14, 1, 2],
    [-7, -20, -8],
    [-27, -19, -4],
    [-19, 4, -4],
    [-15, 4, -4],
    [-11, 4, -4],
    [-31, 8, 2],
    [-151, 5, 24],
    [37, -38, -27],
    [-7, 4, -4],
    [-30, -2, 3],
    [41, -38, -27],
    [-7, -6, -3],
    [-26, -2, 3],
    [-49, 15, 2],
    [-22, -2, 3],
    [17, -20, -16],
    [-10, 11, -4],
    [-55, 6, 7],
    [33, -44, -28],
    [-15, -12, -4],
    [-31, 2, 1],
    [-35, 41, -12],
    [-11, -12, -4],
    [-31, 41, -12],
    [-71, -3, 12],
    [-23, 2, 1],
    [1, -2, -5],
    [-11, 2, 1],
    [-107, 5, 16],
    [1, -22, -11],
    [22, -26, -17],
    [-79, 4, 12],
    [-55, 10, 5],
    [-39, -14, 1],
    [-31, 38, -11],
    [-25, 22, -6],
    [-23, -4, 0],
    [-21, 22, -6],
    [-19, -4, 0],
    [-39, 0, 6],
    [-15, -4, 0],
    [-35, 0, 6],
    [-7, -28, -12],
    [9, -8, -6],
    [-11, -4, 0],
    [-47, -20, 0],
    [-53, 7, 6],
    [-26, 13, -1],
    [-47, 4, 4],
    [-6, -11, -5],
    [-47, -6, 5],
    [-2, -11, -5],
    [-66, -2, 11],
    [-39, 4, 4],
    [1, -14, -7],
    [-62, -2, 11],
    [-18, -10, -1],
    [-39, -6, 5],
    [-14, 3, 0],
    [-35, 4, 4],
    [-11, 3, 0],
    [-10, 3, 0],
    [-9, 3, 0],
    [-35, 33, -8],
    [27, -25, -18],
    [-50, 11, 4],
    [-5, 6, -6],
    [-55, 40, -8],
    [-95, -4, 16],
    [-115, -3, 20],
    [-47, -12, 4],
    [-63, 2, 9],
    [-13, 7, -2],
    [-59, 2, 9],
    [-11, 7, -2],
    [-9, 7, -2],
    [38, -35, -25],
    [-10, -3, -1],
    [-127, 4, 20],
    [-6, 7, -2],
    [-6, -3, -1],
    [-2, -3, -1],
    [-25, 14, -2],
    [-23, 14, -2],
    [47, -42, -30],
    [-19, 17, -8],
    [-34, 5, 3],
    [-13, -9, -2],
    [-151, 2, 25],
    [-55, -4, 8],
    [-30, 5, 3],
    [15, -20, -13],
    [-43, 25, -4],
    [-39, 25, -4],
    [-54, 3, 8],
    [-79, -6, 13],
    [-7, 8, -3],
    [-25, -1, 2],
    [-55, 32, -4],
    [-3, -2, -2],
    [-2, -5, -4],
    [-1, -2, -2],
    [-21, -1, 2],
    [1, -2, -2],
    [2, -5, -4],
    [-17, -1, 2],
    [5, -5, -4],
    [-159, -3, 28],
    [-15, -1, 2],
    [-135, -4, 24],
    [-13, -1, 2],
    [-87, -12, 12],
    [-33, 6, 2],
    [11, -12, -9],
    [-171, 4, 28],
    [13, -12, -9],
    [14, -12, -9],
    [-79, 30, 1],
    [-46, -3, 7],
    [-42, -3, 7],
    [-19, 19, -5],
    [45, -47, -32],
    [-11, 9, -4],
    [3, -18, -10],
    [25, -22, -16],
    [-53, 4, 7],
    [7, -18, -10],
    [-195, 2, 33],
    [3, -4, -5],
    [-43, 17, 0],
    [33, -29, -21],
    [-15, 0, 1],
    [-11, 0, 1],
    [-9, 0, 1],
    [-63, 24, 0],
    [-7, 0, 1],
    [-6, 0, 1],
    [-59, 24, 0],
    [-35, 30, -7],
    [-15, 16, -12],
    [37, -39, -28],
    [41, -39, -28],
    [-23, 7, 1],
    [-55, 66, -19],
    [-37, -2, 6],
    [-13, 4, -1],
    [5, -10, -6],
    [-15, -6, 0],
    [-51, 66, -19],
    [-35, -2, 6],
    [-57, -1, 10],
    [-15, 20, -6],
    [-14, 20, -6],
    [-9, 4, -1],
    [-7, 4, -1],
    [-5, 4, -1],
    [5, -7, -12],
    [-33, 27, -6],
    [-31, 24, -8],
    [-27, 1, 0],
    [14, -17, -11],
    [-23, 24, -8],
    [-19, 1, 0],
    [57, -56, -40],
    [-86, -3, 15],
    [-19, 24, -8],
    [-15, 1, 0],
    [61, -56, -40],
    [1, 0, -12],
    [-11, 1, 0],
    [-15, 14, -7],
    [45, -55, -36],
    [-31, 2, 4],
    [-7, 1, 0],
    [-6, 1, 0],
    [-5, 1, 0],
    [-3, 1, 0],
    [5, -23, -12],
    [-51, 9, 4],
    [-97, 4, 15],
    [113, -98, -71],
    [-30, 31, -8],
    [-47, 9, 4],
    [-3, 1, -8],
    [73, -66, -47],
    [-43, 22, -3],
    [-39, 22, -3],
    [-63, 16, 4],
    [-75, 97, -28],
    [-7, -5, -1],
    [-29, -4, 3],
    [-25, -4, 3],
    [-7, 8, -8],
    [65, -72, -48],
    [-7, -2, -7],
    [-55, 58, -15],
    [-3, -15, -8],
    [1, -2, -7],
    [-45, 42, -10],
    [22, -19, -14],
    [21, -26, -19],
    [-27, 3, 3],
    [25, -26, -19],
    [-263, 4, 44],
    [29, -26, -19],
    [-7, -8, -8],
    [-42, 10, 3],
    [-19, 6, -3],
    [1, -8, -8],
    [-63, 1, 8],
    [-15, 6, -3],
    [5, -8, -8],
    [-59, 1, 8],
    [-11, 6, -3],
    [9, -8, -8],
    [-34, 23, -4],
    [-11, -7, -4],
    [-7, 6, -3],
    [17, -32, -20],
    [-51, 1, 8],
    [-39, 52, -16],
    [9, -8, -16],
    [-3, -7, -4],
    [57, -50, -39],
    [5, -31, -16],
    [-47, 14, 1],
    [1, -7, -4],
    [-91, 9, 12],
    [3, -7, -4],
    [-17, -3, 2],
    [17, -18, -15],
    [21, -18, -15],
    [-83, 22, 5],
    [33, -42, -27],
    [6, -14, -9],
    [9, -14, -9],
    [10, -14, -9],
    [-7, 0, -4],
    [-18, 17, -5],
    [17, -24, -16],
    [-14, 17, -5],
    [-49, 63, -18],
    [-13, 17, -5],
    [21, -24, -16],
    [5, -10, -11],
    [-31, 8, 0],
    [9, -10, -11],
    [-79, -7, 12],
    [-31, -2, 1],
    [-6, 7, -4],
    [-27, 8, 0],
    [-23, 8, 0],
    [25, -34, -23],
    [-23, -2, 1],
    [-19, -2, 1],
    [2, -6, -5],
    [-15, -2, 1],
    [6, -6, -5],
    [7, -6, -5],
    [-7, -26, -11],
    [-38, 15, 0],
    [-11, -2, 1],
    [-10, -2, 1],
    [1, -16, -12],
    [-39, 44, -12],
    [-99, 1, 16],
    [9, -16, -12],
    [-31, -8, 0],
    [-95, 1, 16],
    [-47, 6, 5],
    [-2, 1, -5],
    [17, -16, -12],
    [-139, 9, 20],
    [-23, -8, 0],
    [-19, -8, 0],
    [-87, 14, 9],
    [-17, 18, -6],
    [-10, 2, -1],
    [-7, 2, -1],
    [-6, 2, -1],
    [-3, 2, -1],
    [-2, 2, -1],
    [26, -23, -17],
    [-7, -18, -7],
    [-47, -10, 5],
    [-18, 9, -1],
    [5, -5, -6],
    [-35, 0, 4],
    [-31, 0, 4],
    [-27, 0, 4],
    [-31, 29, -8],
    [-1, -4, -2],
    [-71, 8, 8],
    [-27, 29, -8],
    [-67, 8, 8],
    [-42, 7, 4],
    [-15, 13, -3],
    [-63, -2, 9],
    [-67, 37, -4],
    [-15, -10, -3],
    [-55, -2, 9],
    [-11, -10, -3],
    [-5, 3, -2],
    [-30, -6, 3],
    [-51, -2, 9],
    [-3, 3, -2],
    [-95, 6, 13],
    [-91, 6, 13],
    [-23, 33, -10],
    [-17, 10, -2],
    [-159, 8, 24],
    [19, -21, -14],
    [-23, -16, -4],
    [-15, 10, -2],
    [-63, -8, 8],
    [-13, 10, -2],
    [-50, 2, 7],
    [-26, 1, 3],
    [-46, 2, 7],
    [-22, 1, 3],
    [1, -3, -3],
    [2, -3, -3],
    [30, -31, -21],
    [3, -3, -3],
    [-22, 30, -9],
    [-21, 30, -9],
    [-47, -18, 1],
    [-83, 0, 12],
    [-11, 14, -4],
    [-79, 0, 12],
    [-35, 21, -4],
    [-75, 0, 12],
    [-31, 21, -4],
    [-50, -1, 8],
    [-71, 0, 12],
    [15, -13, -10],
    [-46, -1, 8],
    [-2, -9, -4],
    [-19, 5, 1],
    [-27, 34, -11],
    [-71, 29, 0],
    [-35, 12, 1],
    [-99, -2, 17],
    [69, -59, -44],
    [-187, 1, 32],
    [-43, 3, 6],
    [1, -2, -4],
    [-42, 3, 6],
    [2, -2, -4],
    [-18, -1, 0],
    [35, -30, -22],
    [-14, -1, 0],
    [-7, -1, 0],
    [-6, -1, 0],
    [-15, 18, -11],
    [-3, -1, 0],
    [-99, -8, 16],
    [-1, -8, -5],
    [3, -8, -5],
    [-15, 6, 0],
    [5, -8, -5],
    [-14, -4, 1],
    [-39, 13, 0],
    [-35, 13, 0],
    [77, -75, -52],
    [-31, 26, -7],
    [-63, 72, -20],
    [-27, 26, -7],
    [101, -86, -63],
    [-23, 26, -7],
    [-39, 4, 5],
    [-9, 0, -1],
    [-7, 0, -1],
    [-5, 0, -1],
    [-3, 0, -1],
    [-1, 0, -1],
    [9, -11, -12],
    [-143, -2, 25],
    [-33, 46, -14],
    [-89, 3, 14],
    [73, -67, -48],
    [-63, 2, 10],
    [29, -35, -24],
    [-37, 8, 3],
    [-13, 7, -1],
    [33, -35, -24],
    [-13, -6, -2],
    [9, -10, -8],
    [-38, 37, -9],
    [-9, -6, -2],
    [-7, -6, -2],
    [-5, -6, -2],
    [-25, -2, 4],
    [-51, 28, -4],
    [-3, -3, -8],
    [-47, 28, -4],
    [-43, 5, 4],
    [-51, 57, -16],
    [-39, 5, 4],
    [-47, 57, -16],
    [-11, 11, -3],
    [3, -16, -9],
    [-39, 18, -3],
    [93, -84, -60],
    [7, -16, -9],
    [-33, -8, 3],
    [-79, 13, 8],
    [-31, 18, -3],
    [-3, 1, -2],
    [25, -27, -20],
    [-7, 4, -8],
    [29, -27, -20],
    [37, -51, -32],
    [-17, 2, 2],
    [-3, 4, -8],
    [-71, 26, 1],
    [-7, -19, -8],
    [-15, 5, -4],
    [-11, 5, -4],
    [-7, 5, -4],
    [-26, 22, -5],
    [-45, 0, 7],
    [-27, 12, -4],
    [1, -5, -3],
    [-19, -1, 3],
    [-41, 0, 7],
    [2, -5, -3],
    [-23, 12, -4],
    [89, -76, -56],
    [-19, 12, -4],
    [-109, 2, 18],
    [-42, 29, -5],
    [-15, 12, -4],
    [21, -19, -16],
    [49, -44, -32],
    [33, -30, -27],
    [-11, 12, -4],
    [-15, -11, -4],
    [-11, -11, -4],
    [-3, -35, -16],
    [13, -15, -10],
    [-7, -11, -4],
    [57, -54, -39],
    [-51, 49, -12],
    [61, -54, -39],
    [-15, 3, 1],
    [17, -22, -15],
    [-39, 10, 1],
    [25, -46, -27],
    [-83, 5, 12],
    [21, -22, -15],
    [-35, 10, 1],
    [-31, 10, 1],
    [-6, 6, -5],
    [41, -36, -28],
    [-7, -4, -4],
    [-27, -3, 0],
    [-3, -4, -4],
    [1, -4, -4],
    [-19, -3, 0],
    [17, -52, -28],
    [-37, 1, 6],
    [13, -28, -16],
    [-11, -3, 0],
    [1, -14, -11],
    [-9, -3, 0],
    [-3, -27, -12],
    [-43, -19, 0],
    [-7, -3, 0],
    [53, -46, -35],
    [5, -14, -11],
    [9, -14, -11],
    [65, -70, -47],
    [13, -14, -11],
    [-23, 4, 0],
    [-2, -10, -5],
    [-46, 21, -1],
    [-19, 4, 0],
    [1, -10, -5],
    [-15, 4, 0],
    [-11, 4, 0],
    [-10, 4, 0],
    [1, -20, -12],
    [-55, 12, 4],
    [53, -52, -36],
    [9, -20, -12],
    [-7, -6, -7],
    [-95, -3, 16],
    [-95, 20, 8],
    [-47, 2, 5],
    [-91, -3, 16],
    [1, -6, -7],
    [-19, 24, -7],
    [-39, 2, 5],
    [-18, 24, -7],
    [5, -6, -7],
    [-71, 48, -8],
    [-47, 54, -15],
    [-35, 2, 5],
    [-9, 8, -2],
    [17, -30, -19],
    [-10, -2, -1],
    [-79, 10, 9],
    [-7, -2, -1],
    [21, -30, -19],
    [-6, -2, -1],
    [-3, -2, -1],
    [-2, -2, -1],
    [-25, 15, -2],
    [-119, 18, 13],
    [-47, -4, 4],
    [-19, 2, -3],
    [1, -12, -8],
    [-83, 1, 14],
    [-14, 5, -1],
    [-15, 2, -3],
    [-39, -4, 4],
    [-34, 6, 3],
    [-10, 5, -1],
    [-11, 2, -3],
    [-35, -4, 4],
    [13, -36, -20],
    [-9, 5, -1],
    [9, -12, -8],
    [10, -12, -8],
    [11, -12, -8],
    [-7, 2, -3],
    [-51, -3, 8],
    [-3, 2, -3],
    [-47, -3, 8],
    [-27, 25, -8],
    [-23, 25, -8],
    [-23, -14, -3],
    [-19, 25, -8],
    [-63, -6, 9],
    [-19, -14, -3],
    [2, -18, -9],
    [-11, 9, -3],
    [-9, -1, -2],
    [-59, 33, -4],
    [-5, -1, -2],
    [-3, -1, -2],
    [-1, -1, -2],
    [1, -1, -2],
    [-15, 0, 2],
    [-14, 0, 2],
    [-13, 0, 2],
    [-87, 2, 13],
    [-83, 2, 13],
    [-33, 7, 2],
    [-29, 7, 2],
    [10, -11, -9],
    [-31, -6, 1],
    [-3, 3, -4],
    [-27, -6, 1],
    [-3, -7, -3],
    [-25, 20, -5],
    [-23, -6, 1],
    [-15, -30, -11],
    [-42, -2, 7],
    [-19, -6, 1],
    [-54, 5, 7],
    [7, -17, -10],
    [-35, -12, 0],
    [-27, 11, 0],
    [-10, -13, -4],
    [-23, -36, -12],
    [-31, 40, -12],
    [-71, -4, 12],
    [-11, 1, 1],
    [-9, 1, 1],
    [-78, 3, 12],
    [-103, -6, 17],
    [-55, 38, -7],
    [27, -34, -22],
    [-41, -1, 6],
    [-19, 21, -6],
    [-37, -1, 6],
    [5, -9, -6],
    [6, -9, -6],
    [-35, -1, 6],
    [-14, -5, 0],
    [7, -9, -6],
    [-127, 2, 21],
    [23, -20, -17],
    [-25, 12, -1],
    [39, -44, -29],
    [101, -87, -64],
    [61, -55, -40],
    [-34, 3, 4],
    [-11, 2, 0],
    [-31, 3, 4],
    [-7, 2, 0],
    [-6, 2, 0],
    [-5, 2, 0],
    [-35, 32, -8],
    [-115, -4, 20],
    [-29, -17, -2],
    [-23, 22, -7],
    [-67, 17, 4],
    [-13, 6, -2],
    [-51, 68, -20],
    [-13, -4, -1],
    [-9, 6, -2],
    [9, -8, -7],
    [-7, 6, -2],
    [-107, 25, 8],
    [-5, 6, -2],
    [-7, -4, -1],
    [-6, -4, -1],
    [-5, -4, -1],
    [53, -47, -36],
    [-26, -3, 3],
    [-7, 9, -8],
    [-22, -3, 3],
    [-33, 4, 3],
    [93, -82, -59],
    [-15, 16, -8],
    [-13, -10, -2],
    [-29, 4, 3],
    [-27, 4, 3],
    [-27, 17, -4],
    [-23, 17, -4],
    [-19, 17, -4],
    [-3, -7, -8],
    [45, -39, -32],
    [5, -7, -8],
    [-39, 24, -4],
    [-51, 2, 8],
    [-39, 53, -16],
    [-29, -2, 2],
    [21, -31, -20],
    [-79, 32, 0],
    [-25, -2, 2],
    [25, -31, -20],
    [-27, 14, -3],
    [-27, 37, -11],
    [-21, -2, 2],
    [-23, 14, -3],
    [-17, -2, 2],
    [5, -6, -4],
    [-15, -2, 2],
    [-19, 14, -3],
    [-63, 22, 1],
    [-11, 1, -4],
    [-15, 14, -11],
    [-53, 6, 6],
    [13, -13, -9],
    [-3, 1, -4],
    [9, -10, -15],
    [-3, -12, -5],
    [-22, 18, -5],
    [-25, 34, -10],
    [-18, 18, -5],
    [-15, 18, -5],
    [-15, 8, -4],
    [21, -23, -16],
    [-19, -15, -4],
    [-58, 26, -1],
    [-11, -39, -16],
    [5, -19, -10],
    [-15, -15, -4],
    [-7, 8, -4],
    [-73, 4, 11],
    [-23, 9, 0],
    [-47, 16, 0],
    [-43, 16, 0],
    [5, -5, -5],
    [-39, 16, 0],
    [1, -2, -11],
    [-11, -1, 1],
    [-31, 0, 5],
    [-43, 45, -12],
    [-29, 0, 5],
    [5, -15, -12],
    [-83, 53, -8],
    [41, -40, -28],
    [13, -15, -12],
    [-2, 2, -5],
    [-27, -7, 0],
    [17, -15, -12],
    [-115, 9, 16],
    [-19, -7, 0],
    [-61, -2, 10],
    [-63, 14, 5],
    [-17, 19, -6],
    [-57, -2, 10],
    [-7, 3, -1],
    [-6, 3, -1],
    [-3, 3, -1],
    [53, -50, -35],
    [-7, 6, -7],
    [-22, 10, -1],
    [-43, 1, 4],
    [-39, 1, 4],
    [33, -32, -24],
    [-62, 18, 3],
    [-35, 1, 4],
    [37, -32, -24],
    [-27, 1, 4],
    [1, -24, -12],
    [-75, 9, 8]
  ];
  */

  import "absolute_field.m" : slow_disc, class_number_and_disc, coerce_sub;

  // Third pass. Compute ring of integers, class numbers, and unit index for new keys
  NK := RDiscs diff Keys(B);
  vprintf HilbertModularForms, 1 : "Pass 2 finished at %o. Now computing class numbers and unit indices for %o fields. \n", Cputime(), #NK;

  hplus := NarrowClassNumber(M); // Narrow class number

  for d in NK do
    // h, w, DD := ClassNumberandUnitIndex(ZF, d, hplus : UseCache := UseCache, Cache := Cache); // Class group of K and Hasse Unit index
    // !!! This change makes an improvement of x 4, no idea why!!!
    h, w, DD := class_number_and_disc(ZF, d, slow_disc, coerce_sub);
    // K = F(sqrt(-d))
    // h = h(K)
    // DD = disc(K)
    B[d] := <h, w, DD>;
  end for;

  if SaveAndLoad then
    SaveTriples(B);
  end if;


  // Fourth Pass. Removing pairs where ff/aa is not integral
  vprintf HilbertModularForms, 1 : "Pass 3 finished at %o. Now removing pairs where ff/aa is not integral. \n", Cputime();

  for mm in ideals do
    for aa in Creps do
      L := [];
      for i in A[mm][aa] do
        D := i[3];
        d, c := Explode( Hash[D] );
        f := M`Automorphisms[ Integers()!c ];
        DD := ZF !! f( B[d][3] ); // Discriminant
        ff := ideal < ZF | D*ZF * DD^(-1) >; // Conductor (squared)
        // remove pairs where ff/aa is not integral
        if ff subset aa^2 then
          L cat:= [ [i[1], i[2], d, c] ];
        end if;
      end for;
      A[mm][aa] := L;
    end for;
  end for;

  // verbose printing
  vprintf HilbertModularForms, 1 : "Pass 4 finished at %o. \n", Cputime();

  // Assign
  M`PrecomputationforTrace := A;
  M`ClassNumbersPrecomputation := B;

end intrinsic;


intrinsic PrecomputeTraceForm(M::ModFrmHilDGRng : UseCache := false, Cache := AssociativeArray())
  { Precomputes values to generate traceforms tr }
  HMFTracePrecomputation(M, Ideals(M) : UseCache := UseCache, Cache := Cache);
end intrinsic;


intrinsic PrecomputeTraceForms(M::ModFrmHilDGRng, L::SeqEnum[RngOrdIdl] : UseCache := false, Cache := AssociativeArray())
  {Given a list of ideals L = [aa,bb, ...], precomputes values to generate traceforms t_aa, t_bb, ... }
  A := SetToSequence({ ii * aa : ii in Ideals(M), aa in L }); // Set of ideals
  HMFTracePrecomputation(M,A : UseCache:=UseCache, Cache:=Cache);
end intrinsic;


/* Caching Local Squares
// Computing Artin symbols is the 3rd most expensive computation for the trace code (after class numbers and unit indices).
To compute the Artin symbol (K/pp) for the extension K = F[x] / (x^2 - D) and a prime pp, we need to
  (1) Compute the ring of integers ZK and check if pp | disc(ZK) => return 0
  (2) Check if D is a local square in the completion F_pp => return 1, else -1
Since the local square computation is performed many times, we store the results to M to avoid repeating computations */
intrinsic LocalSquare(M::ModFrmHilDGRng, d::RngOrdElt, pp::RngOrdIdl) -> RngIntElt
  {Checks if D is a local square in the completion F_pp}

  // initialize - LocalSquares[pp]
  if not IsDefined(M`LocalSquares,pp) then
    M`LocalSquares[pp] := AssociativeArray();
  end if;

  // initialize - LocalSquares[pp][d]
  if not IsDefined(M`LocalSquares[pp],d) then
    M`LocalSquares[pp][d] := IsLocalSquare(d,pp) select 1 else -1;
  end if;

  return M`LocalSquares[pp][d];
end intrinsic;
