%--------------------------------------------------
% Load and Save from files
%--------------------------------------------------


%KB open and save

open_kb(Route,KB):-
	open(Route,read,Stream),
	readclauses(Stream,X),
	close(Stream),
	atom_to_term(X,KB).

readclauses(InStream,W) :-
        get0(InStream,Char),
        checkCharAndReadRest(Char,Chars,InStream),
	atom_chars(W,Chars).

checkCharAndReadRest(-1,[],_) :- !.  % End of Stream	
checkCharAndReadRest(end_of_file,[],_) :- !.

checkCharAndReadRest(Char,[Char|Chars],InStream) :-
        get0(InStream,NextChar),
        checkCharAndReadRest(NextChar,Chars,InStream).

%compile an atom string of characters as a prolog term
atom_to_term(ATOM, TERM) :-
	atom(ATOM),
	atom_to_chars(ATOM,STR),
	atom_to_chars('.',PTO),
	append(STR,PTO,STR_PTO),
	read_from_chars(STR_PTO,TERM).

:- op(800,xfx,'=>').

%-------------------------------------------------
% Save KB
%-------------------------------------------------

save_kb(Name,KB):- 
        decompose_term(KB,NewKB),
	open(Name,write,Stream),
        format(Stream,'[',[]),
        format_kb(NewKB,Stream),
        format(Stream,']',[]),
	close(Stream).

decompose_term([],[]).
decompose_term([class(V,W,X,Y,Z)|More],[[V,W,X,Y,Z]|Tail]):-
         decompose_term(More,Tail).

format_kb([],_):-!.
format_kb([[V,W,[],[],[]]], Stream):-
         format(Stream,'~nclass(~q, ~q, [], [], [])~n',[V,W]),!.         
format_kb([[V,W,X,Y,[]]], Stream):-
         format(Stream,'~nclass(~q, ~q, ~n~5|~q, ~n~5|~q, ~n~5|[])~n',[V,W,X,Y]),!.
format_kb([[V,W,X,Y,Z]], Stream):-
         format(Stream,'~nclass(~q, ~q, ~n~5|~q, ~n~5|~q, ~n~5|[',[V,W,X,Y]),format_indv_kb(Z,Stream), format(Stream,'~n~5|]~n~5|)~n',[]),!.
format_kb([[V,W,[],[],[]]|More], Stream):-
         format(Stream,'~nclass(~q, ~q, [], [], []),~n',[V,W]),format_kb(More,Stream),!.
format_kb([[V,W,X,Y,[]]|More], Stream):-
         format(Stream,'~nclass(~q, ~q, ~n~5|~q, ~n~5|~q, ~n~5|[]~n~5|),~n',[V,W,X,Y]),format_kb(More,Stream),!.
format_kb([[V,W,X,Y,Z]|More], Stream):-
         format(Stream,'~nclass(~q, ~q, ~n~5|~q, ~n~5|~q, ~n~5|[',[V,W,X,Y]),format_indv_kb(Z,Stream), format(Stream,'~n~5|]~n~5|),~n',[]), format_kb(More,Stream),!.

format_indv_kb([],_):-!.
format_indv_kb([Obj],Stream):-
         format(Stream,'~n~10|~q',[Obj]),!.
format_indv_kb([Obj|More],Stream):-
         format(Stream,'~n~10|~q,',[Obj]),format_indv_kb(More,Stream),!.

%------------------------------
% Ejemplo:  
%------------------------------

%Cargar la base en una lista, imprimir la lista en consola y guardar todo en un nuevo archivo.
%No olvides poner las rutas correctas para localizar el archivo kb.txt en tu computadora!!!

ejemplo:-
	open_kb('kb.txt',KB),	write('KB: '),	write(KB),	save_kb('new_kb.txt',KB).
	
%---------------------------------------------------------------------------
% CUERPO DEL PROYECTO DE REPRESENTACIÓN DE CONOCIMIENTO:  
%---------------------------------------------------------------------------

%%---------------------------------------------------------------------------
%% Precondiciones:  
%%---------------------------------------------------------------------------

%%%- Formato de los elementos de la lista (functores)
%%%%- class(nombre_de_la_clase, clase_madre, lista_de_propiedades_de_la_clase, lista_de_relaciones_de_la_clase, lista_de_objetos)

%%%- Formato de la lista de objetos se conforma a su vez de listas del siguiente modo:
%%%%- [id=>nombre_del_objeto, lista_de_propiedades_del_objeto, lista_de_relacion

%%%-------------------------------------------------------
%%% Predicados auxiliares:  
%%%-------------------------------------------------------
member(X, [X|_]).
member(X, [_|T]) :- member(X, T).

extract_facts(List,Facts):-
	extract_facts_helper_using_acc(List,[],Facts).

extract_facts_helper_using_acc([],Facts,Facts). %base case
extract_facts_helper_using_acc([H|T],Acc,Facts):-
	(
	write('Inside extract_facts_helper_using_acc...'),nl,
	\+ member(H, Acc)->
	append(Acc,[H], NewFacts)
	;NewFacts=Acc
	),
	extract_facts_helper_using_acc(T,NewFacts,Facts).



subclase(S, P):- 
	nl,write('subclase predicate start...'),nl,
	write('Clase Padre: '), write(P),nl,
	write('Subclase: '), write(S),nl.
	%class(S, P,_,_,_).

%%%-------------------------------------------------
%%% El siguiente predicate itera TODOS los elementos de la KB, en el orden 
%%% en el que fueron listados en el archivo txt
%%%-------------------------------------------------
iterar_clases([]).
iterar_clases([H|T]):-
	nl,write('iterar_clase predicate TODOS los elementos START...'),nl,
	
	nl,write('H :'),write(H),nl,
	write('T :'),write(T),nl,
	class(CN,_,P,_,M) = H,!,
	write('CN: '),write(CN),nl,
	write('Miembros : '), write(M),nl,
	write('Propiedades: '),write(P),nl,
	%write('Miembros : '), write(M),nl,
	iterar_clases(T),

	nl,write('iterar_clase predicate TODOS los elementos '),write(CN),write(' STOP...'),nl.
%-------------------------------------------------
%%% El siguiente predicate itera los elementos de la KB que sean subclases de la clase de interes 
%%% , en el orden en el que fueron listados en el archivo txt
%-------------------------------------------------
%find_subclasses
iterar_subclases([], Clase, Res):-
	nl,write('base case for iterar_subclass '),write(Clase),nl,
	nl,write('Res :'),write(Res),nl,
	write('End of base case iterar_subclases'),nl.

iterar_subclases([H|T], Clase, Res):-
	nl,write('iterar_subclases para buscar subclases de '),write(Clase),write(' predicate START ...'),nl,
	
	nl,write('H :'),write(H),nl,
	write('T :'),write(T),nl,
	class(CN,Top,_,_,M) = H,!,
	write('CN: '),write(CN),nl,
	write('Miembros de '),write(CN), write( ' : '), write(M),nl,
	write('top : '),write(Top),nl,
	write('Res: '),write(Res),nl,
	write('Es Clase '),write(Clase),write(' igual al top de CN= '),write(CN),write(' CN.top == '),write(Top),write('?'),nl,
	
	(%if 
		(CN == Clase;Top == Clase) -> 
		write('IF--keep iterating...'),nl,
		write('Add '),write(CN), write(' to the list of inheritance ...'),nl,
		append([H],Res,TempRes),
		(	%Si es la clase misma, guardar e iterar sobre el resto de la lista...
			CN == Clase ->
			nl,write(CN),write(' Clase misma...agregar y seguir iterando...'),
			iterar_subclases(T,Clase,TempRes),
			Res = TempRes
			;
			%else es una de las clases hijas, iterar subclases sobre e resto de la lista
			write(CN),write(' Clase hija de '),write(Top), write(' Iterar sobre las clases hijas de '),write(CN),nl,
			iterar_subclases(T,Clase,TempRes),
			%iterar_subclases(KB,CN,TempRes),
			
			Res = TempRes
		),
		iterar_subclases(T, Clase, Res),
		write('*Res: '),write(Res),nl,
		write(TempRes),nl
		;
	%else
		nl,write('ELSE--skipping '),write(CN),nl,
		iterar_subclases(T, Clase, Res)
	),
	nl,write('After iteration of iterar_subclases de '),write(CN),
	nl,write('iterar_subclase predicate para buscar sublcases de '),write(Clase),write(' STOP...'),nl.

	
%%-------------------------------------------------------
%% Predicados para Consultar:  
%%-------------------------------------------------------

%%- Ejemplo de la KB inicial como una lista: 
%%- KB = [class(top, none, [], [], []), class(aves, top, [vuelan], [], []), class(peces, top, [nadan], [], []), class(mamiferos, top, [], [], []), class(aguilas, aves, [], [], [[id=>pedro, [...]|...]]), class(pinguinos, aves, [], [], [[... => ...|...]])].
	
class_extension(Clase, KB, Res):-
	write('class_extension predicate START...'),nl,
	write('KB: '), write(KB),nl,
	write('Clase: '), write(Clase),nl,
	Res=[],
	write('Res: '),write(Res),nl,
	
	% iterar TODOS los elementos de la KB
	%iterar_clases(KB),

	% iterar_clases(KB) y calcular unicamente subclases de la clase de interes
	nl,write('#######Calcular subclases de '), write(Clase),write(' ###########'),nl,

	% metodo recursivo:
	iterar_subclases(KB, Clase, []),

	% metodo de consulta por hechos.
	%write('before extracting facts...'),nl,
	%extract_facts(KB,Facts),
	%write('Facts: '),write(Facts),nl,
	
	%findall(X,member(X,KB),Facts),
	%findall(X, member('class(aves,top,[nadan],[],[])',KB),Facts),
	%member('class(aves,top,[nadan],[],[])', KB).

	%nl,write('Result Facts using findAll : '), write(Facts),
	nl,write('Res after recursive rounds: '), write(Res),
	nl,write('class_extension predicate '),write(Clase),write(' STOP...'),nl.
	
property_extension(Prop,KB,Res):-
	write('property_extension predicate start...'),nl,
	write('KB: '), write(KB),nl,
	write('Property: '), write(Prop),nl,
	
	write('proeperty_extension predicate stop...'),nl.

% El resto de los predicados de consultar van aquí abajo	


%%-------------------------------------------------------
%% Predicados para añadir:  
%%-------------------------------------------------------

%% Predicados para añadir van aquí


%-------------------------------------------------------
% Predicados para eliminar:  
%-------------------------------------------------------

rm_class(Clase, KB, Res_Eliminar).
rm_object(Objeto, KB, Res_Eliminar).	

rm_class_property(Clase, Propiedad, KB, Res_Eliminar).
rm_object_property(Objeto, Propiedad, KB, Res_Eliminar).

rm_class_relation(Clase, Relacion, KB, Res_Eliminar).
rm_object_relation(Objeto, Relacion, KB, Res_Eliminar).

%%-------------------------------------------------------
%% Predicados para modificar:  
%%-------------------------------------------------------

