freeze;

//copy pasted from definite.m and modified

function HeckeOperatorDefiniteBig(M, p : Columns:="all", hack := true)

   assert not assigned M`Ambient; // M is an ambient

   // Caching
   // HeckeBig and HeckeBigColumns must be assigned together

   cached, Tp := IsDefined(M`HeckeBig, p);
   if cached then 
     Tp := Matrix(Tp);
     _, old_cols := IsDefined(M`HeckeBigColumns, p);
     if Columns cmpeq "all" then
       Columns := [1..Ncols(Tp)];
     end if;
     columns := [j : j in Columns | j notin old_cols];
     if IsEmpty(columns) then
       return Tp;
     end if;
   else
     old_cols := [];
     columns := Columns;
   end if;

   A := Algebra(QuaternionOrder(M));
   N := Level(M);
   weight2 := Seqset(Weight(M)) eq {2};
   easy := weight2 and N eq Discriminant(QuaternionOrder(M));
   // easy = basis of big space is given by the rids

   if not assigned M`basis_matrix then
     _ := BasisMatrixDefinite(M : EisensteinAllowed);
   end if;
   dim := Ncols(M`basis_matrix_big);

   F := M`weight_base_field; // = Q for parallel weight 2
   if easy then
     h := dim;
   else
     HMDF := M`ModFrmHilDirFacts; 
     nCFD := [#xx`CFD : xx in HMDF];
     h := #HMDF;
     wd := M`weight_dimension; // = 1 for weight2
   end if;

   // Columns/columns refer to actual columns of the big matrix, 
   // Bcolumns to columns of large blocks, bcolumns to small blocks

   if columns cmpeq "all" then
     columns := [1..dim];
   else
     columns := Sort([Integers()| i : i in columns]);
   end if;
   assert not IsEmpty(columns) and columns subset [1..dim];

   if not weight2 then // currently, higher weight doesn't use Columns
     columns := [1 .. dim];
   end if;

   if easy then
     bcolumns := columns;
     Bcolumns := columns;
   elif columns eq [1 .. dim] then // full matrix 
     bcolumns := [1 .. dim div wd];
     Bcolumns := [1 .. h];
   elif weight2 then 
     bcolumns := columns;
     Bcolumns := [];
     b := 1;
     for i := 1 to #HMDF do
       e := b + nCFD[i] - 1;
       if exists{x: x in [b..e] | x in columns} then
         Append(~Bcolumns, i);
       end if;
       b := e + 1;
     end for;
   else
     bcolumns := [];
     Bcolumns := [];
     b := 1;
     for i := 1 to #HMDF do
       for j := 1 to nCFD[i] do
         e := b + wd - 1;
         if exists{x: x in [b..e] | x in columns} then
           Append(~bcolumns, e div wd);
           Append(~Bcolumns, i);
         end if;
         b := e + 1;
       end for;
     end for;
   end if;

   if not cached then
     Tp := MatrixRing(F, dim) ! 0; 
   end if;

//"Starting with"; Tp;

//"Columns:"; Columns; old_cols; columns; bcolumns; Bcolumns;

   tp := get_tps(M, p : rows:=Bcolumns); // rows in precompute_tps are columns here

   vprintf ModFrmHil: "%o%o column%o%o of big Hecke matrix (norm %o): ", 
                      #columns eq dim select "All " else "", 
                      #columns, 
                      #columns gt 1 select "s" else "", 
                      #columns gt 1 select "" else " (#"*Sprint(columns[1])*")", 
                      Norm(p);
   vtime ModFrmHil:

   if easy then

      for j in Bcolumns, i in [1..h] do 
         bool, tpji := IsDefined(tp, <j,i>);
         if bool then
            Tp[i,j] := #tpji;
         end if;
      end for;

   else

     sm := M`splitting_map;
     
     checkP1 := Valuation(N,p) gt 0;

     inds := [l : l in [1..#HMDF] | nCFD[l] ne 0];
     row := 0; 
     col := 0;

     for m in inds do 
        if m in Bcolumns then
           for l in inds do 
              bool, tpml := IsDefined(tp, <m,l>);
              if bool then
                 if weight2 then

                    PLDl := HMDF[l]`PLD;
                    FDl   := PLDl`FD; 
                    FDm   := HMDF[m]`PLD`FD; 
                    lookup:= PLDl`Lookuptable; 
                    P1rep := PLDl`P1Rep;

                    Tplm := ExtractBlock(Tp, row+1, col+1, #FDl, #FDm);
                    mms := [mm : mm in [1..#FDm] | col+mm in bcolumns];
                    for ll := 1 to #tpml do
                       mat := tpml[ll] @ sm;
                       for mm in mms do 
                          u := mat * FDm[mm];
                          bool, u0 := P1rep(u, checkP1, false);
                          if bool then
                             n := lookup[u0,1]; 
                             // assert n eq Index(HMDF[l]`CFD, n);
                             Tplm[n,mm] +:= 1;
                          end if;
                       end for;
                    end for;
                    InsertBlock(~Tp, Tplm, row+1, col+1);

                 else

                    PLDl  := HMDF[l]`PLD;
                    FDl   := PLDl`FD; 
                    FDm   := HMDF[m]`PLD`FD; 
                    lookup:= PLDl`Lookuptable; 
                    P1rep := PLDl`P1Rep;

                    CFDl := HMDF[l]`CFD; 
                    CFDm := HMDF[m]`CFD; 
                    units1 := HMDF[l]`max_order_units; 
                    weight_map := HMDF[l]`weight_rep; 

                    Tplm := Matrix(F, wd*#CFDl, wd*#CFDm, []);

                    for ll := 1 to #tpml do
                       mat := tpml[ll] @ sm;
                       for mm := 1 to #CFDm do
                          u := mat * FDm[CFDm[mm]];
                          bool, u0 := P1rep(u, checkP1, false);
                          if bool then
                             elt_data := lookup[u0]; 
                             n := Index(CFDl, elt_data[1]);
                             if n ne 0 then
                                quat1 := units1[elt_data[2]]^-1 * tpml[ll]; 
                                X := ExtractBlock(Tplm, (n-1)*wd+1, (mm-1)*wd+1, wd, wd);
                                X +:= weight_map(quat1);
                                InsertBlock(~Tplm, X, (n-1)*wd+1, (mm-1)*wd+1);
                             end if;
                          end if;
                       end for;
                    end for;
                    InsertBlock(~Tp, Tplm, row+1, col+1);

                 end if;
              end if;
              row +:= nCFD[l] * wd;
           end for;
        end if;
        col +:= nCFD[m] * wd;
        row := 0;
     end for;

   end if;

   // new columns were computed, so renew the cache
   M`HeckeBig[p] := SparseMatrix(Tp);
   M`HeckeBigColumns[p] := Sort(old_cols cat columns);
//"Now got columns",  M`HeckeBigColumns[p]; M`HeckeBig[p];

   // Check Hecke invariance of Eisenstein subspace and its complement
   if debug and M`HeckeBigColumns[p] eq [1..dim] then
     if assigned M`InnerProductBig and Norm(p + N) eq 1 
        and p@@cl eq NCl.0 where NCl, cl is NarrowClassGroup(BaseField(M))
     then
       assert Tp * M`InnerProductBig eq M`InnerProductBig * Transpose(Tp);
     end if;
     if assigned M`eisenstein_basis then
       assert Rowspace(M`eisenstein_basis * Tp) subset Rowspace(M`eisenstein_basis);
     end if;
     if assigned M`basis_matrix then
       printf "[debug] Checking space is preserved by Tp: "; time 
       assert Rowspace(M`basis_matrix * Tp) subset Rowspace(M`basis_matrix);
     end if;
   end if;

   return Tp;
end function;



// TO DO: columns option

function AtkinLehnerDefiniteBig(M, p)

   assert not assigned M`Ambient; // M is an ambient

   if not assigned M`ALBig then
      M`ALBig := AssociativeArray(Parent(p));
   else
      cached, Wp := IsDefined(M`ALBig, p);
      if cached then
         return Matrix(Wp);
      end if;
   end if;

   N := Level(M) / Discriminant(QuaternionOrder(M));
   e := Valuation(N, p); 
   assert e gt 0;
   pe := p^e;
   NN := N/pe;
   assert ISA(Type(NN), RngOrdIdl); // integral
   ZF := Order(p);
   quope, modpe := quo<ZF|pe>;
   _, P1pe := ProjectiveLine(quope : Type:="Vector");
   // TO DO: if pe = N, use existing P1N

   if not assigned M`basis_matrix then
     _ := BasisMatrixDefinite(M : EisensteinAllowed);
   end if;
   dim := Ncols(M`basis_matrix_big);

   HMDF := M`ModFrmHilDirFacts; 
   nCFD := [#xx`CFD : xx in HMDF];
   h := #HMDF;
   wd := M`weight_dimension; // = 1 for weight2
   F := M`weight_base_field; // = Q for weight2
   sm := M`splitting_map;

   tp := get_tps(M, pe);

   weight2 := Seqset(Weight(M)) eq {2};

   Wp := MatrixRing(F, dim) ! 0; 

   // block[l] = sum of dimensions of blocks [1..l-1]
   block := [0 : l in [1..#HMDF]];
   for l := 1 to #HMDF-1 do
      block[l+1] := block[l] + nCFD[l];
   end for;

   inds := [l : l in [1..#HMDF] | nCFD[l] ne 0];

   for m in inds do 
      ls := {@ l : l in inds | IsDefined(tp, <m,l>) @};

      tp_split_N := AssociativeArray(ls);
      tp_split_pe := AssociativeArray(ls);
      tp_ker := AssociativeArray(ls);
      tp_elt := AssociativeArray(ls); // used when not weight2
      for l in ls do 
         tp_split_N[l]  := {@ @};
         tp_split_pe[l] := {@ @};
         tp_ker[l]      := {@ @};
         tp_elt[l]      := {@ @};
         for t in tp[<m,l>] do
            // this is where we get rid of the extra elements in tps (if e > 1)
            tsN := t@sm;
            tspe := Matrix(2, [x@modpe : x in Eltseq(Transpose(tsN))]);
            bool, tk := P1pe(ChangeRing(Kernel(tspe).1,ZF), true, false);
            if bool then
               Include(~tp_split_N[l],  tsN);
               Include(~tp_split_pe[l], tspe);
               Include(~tp_ker[l],      tk);
               Include(~tp_elt[l],      t);
            end if;
         end for;
         if debug then
            assert forall{t : t in tp_split_pe[l] | Determinant(t) eq 0};
            assert forall{t : t in tp_split_pe[l] | #Kt eq Norm(pe) and Kt subset sub<Kt|Kt.1> where Kt is Kernel(t)};
            assert forall{t : t in tp_split_pe[l] | #It eq Norm(pe) and It subset sub<It|It.1> where It is Image(t)};
            // Kt and It are rank 1 modules; basis in Howell normal form can have 2 elements, but the first generates it
         end if;
      end for;
      if debug and #inds eq #HMDF then
         // The elements tp[<m,?>] are in bijection with P1 under the map t :-> ker(t mod p)
         assert # &join [tp_ker[l] : l in ls] eq (Norm(p)+1)*Norm(p)^(e-1);
      end if;
   
      FDm := HMDF[m]`PLD`FD; 
      for mm in HMDF[m]`CFD do

         // identify the unique t which kills this element in P1 mod p
         _, vpe := P1pe(Eltseq(FDm[mm]), false, false);
         if debug then
            assert #{l : l in ls | vpe in tp_ker[l]} eq 1;
         end if;
         for l_ in ls do
            k := Index(tp_ker[l_], vpe);
            if k ne 0 then
               l := l_;
               break;
            end if;
         end for;

         // get image mod p and then mod N
         imt := Image(tp_split_pe[l,k]);  
         impe := ChangeUniverse(Eltseq(Basis(imt)[1]), ZF);
         if IsOne(NN) then
            imN := impe;
         else
            tv := Eltseq(tp_split_N[l,k] * FDm[mm]);
            imN := [ZF| ChineseRemainderTheorem(pe, NN, impe[i], tv[i]) : i in [1,2]];
         end if;
         // get rep in P1 mod N
         PLDl := HMDF[l]`PLD;
         if debug then
            bool, imN := PLDl`P1Rep(Matrix(1, imN), true, false); assert bool;
         else
            _, imN := PLDl`P1Rep(Matrix(1, imN), false, false);
         end if;

         if weight2 then

            ll := PLDl`Lookuptable[imN, 1];  
            assert ll gt 0;

            r := block[l] + ll;
            c := block[m] + mm;
            assert Wp[r,c] eq 0;
            Wp[r,c] := 1;

         else

            ll, u := Explode(PLDl`Lookuptable[imN]);
            assert ll gt 0;
            rr := Index(HMDF[l]`CFD, ll) - 1;
            cc := Index(HMDF[m]`CFD, mm) - 1;
            assert rr ge 0;
            assert cc ge 0;
            if rr ge 0 then
               r := (block[l] + rr) * wd + 1;
               c := (block[m] + cc) * wd + 1;
               assert IsZero(Submatrix(Wp, r, c, wd, wd));

               units1     := HMDF[l]`max_order_units; 
               weight_map := HMDF[l]`weight_rep; 

               quat1 := units1[u] ^ -1 * tp_elt[l,k];
               InsertBlock(~Wp, weight_map(quat1), r, c);
            end if;

         end if;
           
      end for; // mm
   end for; // m
  
   M`ALBig[p] := SparseMatrix(Wp);
   return Wp;
end function;
