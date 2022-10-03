intrinsic GetAllEllipticTraces(K::FldNum) -> SeqEnum[FldNumElt]
{Returns all the possible traces of eliptic elements in the field, i.e. alpha in Integers(K) such that trace(alpha) << 4.}
  Z_K := Integers(K);																   
  real := Matrix([RealEmbeddings(x) : x in Basis(Z_K)]);
  lat := Lattice(real);
  sv := ShortVectors(lat,4*Degree(K) : PositiveCoordinates := false);
  vecs := [v[1] : v in sv | &and[Abs(v[1][i]) lt 4.0 : i in [1..Degree(K)]]];
  vecs cat:= [-v : v in vecs];
  elts := [Z_K!Coordinates(v) : v in vecs];
  return [K!x : x in elts] cat [K!0];												     
end intrinsic;
    
