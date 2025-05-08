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

%%%- Formato de los elementos de la lista (funtores)
%%%%- class(nombre_de_la_clase, clase_madre, lista_de_propiedades_de_la_clase, lista_de_relaciones_de_la_clase, lista_de_objetos)

%%%- Formato de la lista de objetos se conforma a su vez de listas del siguiente modo:
%%%%- [id=>nombre_del_objeto, lista_de_propiedades_del_objeto, lista_de_relacion

%%%-------------------------------------------------------
%%% Predicados auxiliares:  
%%%-------------------------------------------------------

subclase(S, P):- 
	write('subclase predicate start...'),nl,
	write('Clase Padre: '), write(P),nl,
	write('Subclase: '), write(S),nl,
	class(S, P,_,_,_).

iterar_clases([], Clase).
iterar_clases([H|T], Clase):-
	write('iterar_clase predicate start...'),nl,
	write('Class: '), writeln(H),
	H(Nombre,_,_,_),
	write('Nombre de la clase: '),Nombre,nl,
	Clase == Nombre ->
	subclase(Subclase, Clase);
	iterar_clases(T,Clase).
	%iterar_clases(T).
	

	
	
%%-------------------------------------------------------
%% Predicados para Consultar:  
%%-------------------------------------------------------

%%- Ejemplo de la KB inicial como una lista: 
%%- KB = [class(top, none, [], [], []), class(aves, top, [vuelan], [], []), class(peces, top, [nadan], [], []), class(mamiferos, top, [], [], []), class(aguilas, aves, [], [], [[id=>pedro, [...]|...]]), class(pinguinos, aves, [], [], [[... => ...|...]])].
	
class_extension(Clase, KB, Res):-
	write('class_extension predicate start...'),nl,
	write('KB: '), write(KB),nl,
	write('Clase: '), write(Clase),nl,
	
	%H(Nombre,_,_,_),
	%write('Nombre: '), write(Nombre),nl,
	
	% iterar_clases(KB) y calcular subclases unicamente de la clase de interes
	write('Calcular subclases de '), write(Clase),nl,
	iterar_clasess(KB, 'aves'),
	
	write('Extension: '), write(Res),
	write('class_extension predicate stop...').
	
property_extension(Prop,KB,Res):-
	write('property_extension predicate start...'),nl,
	write('KB: '), write(KB),nl,
	write('Property: '), write(Prop),nl,
	
	write('proeperty_extension predicate stop...').

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

