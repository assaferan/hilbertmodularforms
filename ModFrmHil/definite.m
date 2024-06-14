// freeze;

import !"Geometry/ModFrmHil/definite.m" : BasisMatrixDefinite, debug;

import "precompute.m" : get_tps;

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

   tp := get_tps(M, p : rows:=Bcolumns, hack := true); // rows in precompute_tps are columns here

   vprintf ModFrmHil: "%o%o column%o%o of big Hecke matrix (norm %o): ", 
                      #columns eq dim select "All " else "", 
                      #columns, 
                      #columns gt 1 select "s" else "", 
                      #columns gt 1 select "" else " (#"*Sprint(columns[1])*")", 
                      Norm(p);
   // vtime ModFrmHil:

   if easy then
       for j in Bcolumns, i in [1..h] do 
	   // hack begins
	   if hack then
	       eps := M`UnitCharacter;
	       Tp[i,j] := 0;
	       for u in Keys(tp) do
		   bool, tpji := IsDefined(tp[u], <j,i>);
		   if bool then 
		       Tp[i,j] +:= (eps@u)*#tpji;
		   end if;
	       end for;
	   else
               bool, tpji := IsDefined(tp, <j,i>);
               if bool then
		   Tp[i,j] := #tpji;
	       end if;
           end if;
	   // hack ends
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
	       // hack begins
	       if hack then
		   eps := M`UnitCharacter;
		   PLDl := HMDF[l]`PLD;
		   FDl   := PLDl`FD; 
		   FDm   := HMDF[m]`PLD`FD; 
		   lookup:= PLDl`Lookuptable; 
		   P1rep := PLDl`P1Rep;
		   if weight2 then
		       Tplm := ExtractBlock(Tp, row+1, col+1, #FDl, #FDm);
		       for v in Keys(tp) do
			   bool, tpml := IsDefined(tp[v], <m,l>);
			   if bool then
			       mms := [mm : mm in [1..#FDm] | col+mm in bcolumns];
			       for ll := 1 to #tpml do
				   mat := tpml[ll] @ sm;
				   for mm in mms do 
				       u := mat * FDm[mm];
				       bool, u0 := P1rep(u, checkP1, false);
				       if bool then
					   n := lookup[u0,1]; 
					   // assert n eq Index(HMDF[l]`CFD, n);
					   // Tplm[n,mm] +:= 1;
					   Tplm[n,mm] +:= eps@v;
				       end if;
				   end for;
			       end for;
			   end if;
		       end for;
		       InsertBlock(~Tp, Tplm, row+1, col+1);
			       
		   else
			       
		       CFDl := HMDF[l]`CFD; 
		       CFDm := HMDF[m]`CFD; 
		       units1 := HMDF[l]`max_order_units; 
		       weight_map := HMDF[l]`weight_rep; 
			       
		       Tplm := Matrix(F, wd*#CFDl, wd*#CFDm, []);
		       for v in Keys(tp) do
			   bool, tpml := IsDefined(tp[v], <m,l>);
			   if bool then
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
					       X +:= (eps@v)*weight_map(quat1);
					       InsertBlock(~Tplm, X, (n-1)*wd+1, (mm-1)*wd+1);
					   end if; // n
				       end if; // bool
				   end for; // mm
			       end for; // ll
			   end if;
		       end for;
		       InsertBlock(~Tp, Tplm, row+1, col+1);
			   
		   end if; // weight2
		       
		   row +:= nCFD[l] * wd;
	       else
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
				       end if; // n
				   end if; // bool
			       end for; // mm
			   end for; // ll
			   InsertBlock(~Tp, Tplm, row+1, col+1);
			   
                       end if; // weight2
		   end if; // bool
		   row +:= nCFD[l] * wd;
	       end if; // hack
	   end for; // l
        end if; // m
        col +:= nCFD[m] * wd;
        row := 0;
     end for; // m
     
   end if; // easy

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

/************************************ Modified intrinsics ************************************/

intrinsic InternalHMFRawHeckeDefinite(M::ModFrmHil, p::RngOrdIdl : hack := true) -> Mtrx
{The Hecke operator T_p on the raw space containing M}

  require not assigned M`Ambient :
         "This space is computed as a subspace of another space: use M`Ambient";

  return HeckeOperatorDefiniteBig(M, p : hack := hack);
end intrinsic;

intrinsic HeckeMatrixRaw(M::ModFrmHil, p::RngOrdIdl : hack := true) -> Mtrx
{"}//"
  require not assigned M`Ambient :
         "This space is computed as a subspace of another space: use M`Ambient";

  return HeckeOperatorDefiniteBig(M, p : hack := hack);
end intrinsic;
