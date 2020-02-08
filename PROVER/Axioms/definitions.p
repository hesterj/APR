include('zfc.ax').

%new
fof(one_to_one, axiom, ![X,Y,Z,Xf]: (one_to_one(Xf) 
	<=> (function(Xf) 
		& 
		(
			(member(ordered_pair(X,Z),Xf) & 
			member(ordered_pair(Y,Z),Xf) ) 
				=> X=Y
		) 
		 
	) ) ).

%Definition of bijection
fof(bijection_def,definition, ![Xf,X,Y]: (bijection(Xf,X,Y)<=>(one_to_one(Xf) & range_of(Xf)=Y & domain_of(Xf)=X) ) ).
/*
%![X,Y,Z,Xf,Xg]:
%Definition of cardinal 2
fof(cardinal_def, definition, 
	( 
		cardinality(X,Y)
			<=> 
			(?[Xf]: ![Xg]: ordinal(Y) & (bijection(Xf,X,Y)) & (member(Z,Y)=> ~bijection(Xg,Z,Y)) 
			) 
		
	)
).
*/

%Definition of cardinal 3
fof(cardinal_def,definition,
	cardinality(X)=Y <=>
		(
			ordinal(Y) &
			(
				?[Xf]: 
					(
					bijection(Xf,X,Y) &
						(
						![Xg,Z]:
							(
							member(Z,Y) => ~bijection(Xg,X,Z)
							)
						)
					)
			)	
		)
	).

%%%%%%%%%%%%%%%%%%%%% Ordinals and Element Relation

fof(element_relation,definition, ![X,Y,Z]: (member(ordered_pair(X,Y),element_relation(A))<=> (member(X,A) & member(Y,A) & member(X,Y) ) )).

fof(ordinals,definition,(
      ( ![A]: (ordinal(A)
    <=> (strict_well_order(element_relation(A),A) 
        & ! [X] :
            ( member(X,A)
           => subclass(X,A) ) ) ) ) ) ).
           
%%%%%%%%%%%%%%%%%%%%%%%%

%fof(idtfun, definition, ![X]:(ident_fun(X)=restrict(identity_relation,X,universal_class)) ).
fof(idtfun, definition, ![X,Y]: (member(Y,ident_fun(X)) <=> ?[Z]:(member(Z,X) & Y = ordered_pair(Z,Z))) ).
fof(idtfun2, definition, ![X,Y]:(member(Y,X)<=>member(ordered_pair(Y,Y),ident_fun(X)) ) ).

