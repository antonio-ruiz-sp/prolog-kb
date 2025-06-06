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

%%%- Formato de la KB:
%%%%- La KB se conforma de una lista de clases, cada una de las cuales tiene un nombre, una clase madre, una lista de propiedades, una lista de relaciones y una lista de objetos.
%%%%- KB = [class(top, none, [], [], []), class(aves, top, [vuelan], [], []), class(peces, top, [nadan], [], []), class(mamiferos, top, [], [], []), class(aguilas, aves, [], [], [[id=>pedro, [...]|...]]), class(pinguinos, aves, [], [], [[... => ...|...]]), class(felinos, mamiferos, [], [], [[...|...]])],

%%%- Formato de los elementos de la lista (functores)
%%%%- class(nombre_de_la_clase, clase_madre, lista_de_propiedades_de_la_clase, lista_de_relaciones_de_la_clase, lista_de_objetos)

%%%- Formato de la lista de objetos se conforma a su vez de listas del siguiente modo:
%%%%- [id=>nombre_del_objeto, lista_de_propiedades_del_objeto, lista_de_relacion

%%%-------------------------------------------------------
%%% Predicados auxiliares:  
%%%-------------------------------------------------------
:- use_module(module/kb_utils).


%member(X, [X|_]).
%member(X, [_|T]) :- member(X, T).





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
	iterar_clases(T),

	nl,write('iterar_clase predicate TODOS los elementos '),write(CN),write(' STOP...'),nl.
%-------------------------------------------------
%%% El siguiente predicate itera los elementos de la KB que sean subclases de la clase de interes 
%%% en el orden en el que fueron listados en el archivo txt
%-------------------------------------------------
% find_subclasses
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

iterar_subclases_1(Clase, [], KB, Res):-
	nl,write('base case for iterar_subclases_1 '),write(Clase),nl,
	nl,write('Res :'),write(Res),nl,
	write('End of base case iterar_subclases_1'),nl.

iterar_subclases_1(Clase,[H|T], KB, Res):-
	nl,write('iterar_subclases_1 para buscar subclases de '),write(Clase),write(' predicate START ...'),nl,
	
	nl,write('H :'),write(H),nl,
	write('T :'),write(T),nl,
	class(CN,Top,_,_,M) = H,!,
	write('CN: '),write(CN),nl,
	write('Miembros de '),write(CN), write( ' : '), write(M),nl,
	write('top : '),write(Top),nl,
	write('Res: '),write(Res),nl,
	nl,write('Res :'),write(Res),nl,
	write('End of base case iterar_subclases_1'),nl.

	

%%-------------------------------------------------------
%% Predicados para Consultar:  
%%-------------------------------------------------------

%%- Ejemplo de la KB inicial como una lista: 
%%- KB = [class(top, none, [], [], []), class(aves, top, [vuelan], [], []), class(peces, top, [nadan], [], []), class(mamiferos, top, [], [], []), class(aguilas, aves, [], [], [[id=>pedro, [...]|...]]), class(pinguinos, aves, [], [], [[... => ...|...]])].
	
% ========================================================================	
class_extension(Clase, KB, Res):-
	debug(class_ext, 'Starting class_extension predicate START...~n',[]),
	debug(class_ext, 'KB: ~q~n', [KB]),
	debug(class_ext, 'Clase: ~q~n', [Clase]),	

	debug(class_ext,'..inside findall for class_extension predicate~n', []),

	findall(ID,
            (   member(class(Clase, _, _, _, Miembros), KB),
				member([id=>ID|_], Miembros)
			),
            DirectInstances),
    findall(SubClassName,
            member(class(SubClassName, Clase, _, _, _), KB),
            SubClasses),
	debug(class_ext,'SubClasses found: ~q~n', [SubClasses]),
    find_subclass_instances(SubClasses, KB, SubClassInstances),
    append(DirectInstances, SubClassInstances, Res),

	debug(class_ext, 'class_extension predicate STOP...~n',[]).

% Predicado auxiliar para encontrar las subclases de una clase.
find_subclass_instances([], _, []):-
	debug(class_ext, 'Base Case.~n',[]).

find_subclass_instances([SubClass|Remaining], KB, AllInstances) :-
	debug(class_ext,'Finding instances for subclass: ~q~n', [SubClass]),
    class_extension(SubClass, KB, SubClassInstances),
    find_subclass_instances(Remaining, KB, RestInstances),
    append(SubClassInstances, RestInstances, AllInstances).

% ========================================================================	
property_extension(Prop, KB, Res):-
	debug(prop_ext, 'Starting property_extension predicate START...~n',[]),
	debug(prop_ext, 'KB: ~q~n', [KB]),
	debug(prop_ext, 'Propiedad: ~q~n', [Prop]),	
	
	findall(
        Id:Value, % Lista en formato Id:Value
        (
            % Iterar las clases en la KB
            member(class(Class, Top, _, _, Miembros), KB),
			debug(prop_ext, 'Processing class: ~q which has Members: ~q~n', [Class, Miembros]),
            % Busca la propiedad en la jerarquía de clases (padre si es necesario)
            check_property_with_inheritance(Prop, Class, Top, KB, InitialValue),
            % Para cada instancia, asigna el valor heredado o el valor del atributo
            member([id=>Id, Propiedades, _], Miembros),
            % Desempaquetar los atributos para buscar la propiedad
            flatten(Propiedades, FlatAttributes),
            % Sobrescribir el valor si la propiedad está definida en los atributos de la instancia
            (   member(Prop=>AttributeValue, FlatAttributes) 
                -> Value = AttributeValue
            ;   Value = InitialValue
            )
        ),
        ResultUnfiltered
    ), 
	debug(prop_ext, 'ResultUnfiltered: ~q~n', [ResultUnfiltered]),
	filter_list(ResultUnfiltered, ResultUnSort),
    % Procesar ResultUnfiltered para eliminar duplicados: conservar el que tenga 'yes' si hay 'no' para el mismo Id
    remove_duplicates_with_preference(ResultUnSort, Res).

	debug(prop_ext, 'propperty_extension predicate STOP..~n').
% ========================================================================

relation_extension(Rel, KB, Res):-
	debug(relation_ext, 'Starting relation_extension predicate START...~n',[]),
	debug(relation_ext, 'KB: ~q~n', [KB]),
	debug(relation_ext, 'Relacion: ~q~n', [Rel]),	
	
	findall(
		Id:Value, % Lista en formato Id:Value
		(
			% Iterar las clases en la KB
			member(class(Class, Top, _, Relations, Miembros), KB),
			debug(relation_ext, '***Processing class: ~q which has Members: ~q and Relations: ~q~n', [Class, Miembros, Relations]),
			% Busca la relación en la jerarquía de clases (padre si es necesario)
			check_relation_with_inheritance(Rel, Class, Top, KB, Value),
			debug(relation_ext, 'Value after checking inheritance: ~q~n', [Value]),
			% Para cada instancia, asigna el valor heredado o el valor del atributo
			member([id=>Id, _, Relaciones], Miembros),
			% Desempaquetar las relaciones para buscar la relación
			flatten(Relaciones, FlatRelations),
			debug(relation_ext, 'FlatRelations: ~q~n', [FlatRelations]),	
			% Sobrescribir el valor si la relación está definida en las relaciones de la instancia
			(   member(Rel=>Value, FlatRelations) 
				-> true
			;   Value = none
			)
		),
		ResultUnfiltered
	), 
	debug(relation_ext, 'ResultUnfiltered: ~q~n', [ResultUnfiltered]),

	filter_list(ResultUnfiltered, ResultUnSort),
	% Procesar ResultUnfiltered para eliminar duplicados: conservar el que tenga 'yes' si hay 'no' para el mismo Id
	remove_duplicates_with_preference(ResultUnSort, Res).

	debug(relation_ext, 'relation_extension predicate STOP..~n').
% ========================================================================

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

