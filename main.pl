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

% Predicado auxiliar para  las subclases de una clase.
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
			%member(class(Class, Top, _, Relations, Miembros), KB),
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

	filter_list1(ResultUnfiltered, ResultUnSort),
	% Procesar ResultUnfiltered para eliminar duplicados: conservar el que tenga 'yes' si hay 'no' para el mismo Id
	remove_duplicates_with_preference(ResultUnSort, Res).

	debug(relation_ext, 'relation_extension predicate STOP..~n').

	filter_list1([], []).
	filter_list1([H|T], [H|Filtered]) :-
	% Verifica si H es una lista con al menos dos elementos
	(   is_list(H), length(H, Len), Len >= 2
	->  % Si es así, verifica si el primer elemento es un ID y el segundo es un valor
		H = [Id, Value|_],
		% Si el valor no es 'none', lo incluye en la lista filtrada
		Value \= none
	;   % Si no es una lista válida, lo omite
		Filtered = T
	),
	filter_list1(T, Filtered).

% ========================================================================
properties_of_individual(obj,KB, Res):-
	debug(props_ind, 'Starting properties_of_individual predicate START...~n',[]),
	debug(props_ind, 'KB: ~q~n', [KB]),
	debug(props_ind, 'Objeto: ~q~n', [obj]),

	findall(
		Id:Value, % Lista en formato Id:Value
		(
			member(class(_, _, Properties, _, Members), KB),
			member([id=>Id, Props, _], Members),
			flatten(Props, FlatProps),
			member(obj=>Value, FlatProps)
		),
		ResultUnfiltered
	), 
	debug(props_ind, 'ResultUnfiltered: ~q~n', [ResultUnfiltered]),
	filter_list(ResultUnfiltered, Res).

	debug(props_ind, 'properties_of_individual predicate STOP..~n').	
	

% ========================================================================
class_properties(obj,KB, Res).
% ========================================================================
relations_of_individual(obj, KB, Res).
% ========================================================================
class_relations(class, KB, Res).


%%-------------------------------------------------------
%% Predicados para añadir:  
%%-------------------------------------------------------

%% Predicados para añadir van aquí

%--------------------------------------------------
% Añadir una nueva clase (add_class/4)
%--------------------------------------------------
add_class(ClassName, ParentClass, CurrentKB, NewKB) :-
    % Verificar que la clase padre exista
    ParentClass == none ; member(class(ParentClass, _, _, _, _), CurrentKB),
    % Verificar que la clase no exista ya
    \+ member(class(ClassName, _, _, _, _), CurrentKB),
    % Construir la nueva clase
    NewClass = class(ClassName, ParentClass, [], [], []),
    % Añadirla a la KB
    
    append(CurrentKB, [NewClass], NewKB).
    %save_kb('new_kb_1_1.txt',NewKB).




%--------------------------------------------------
% Añadir un nuevo objeto (add_object/4)
%--------------------------------------------------
add_object(ObjectName, ClassName, CurrentKB, NewKB) :-
    % 1. Encontrar la clase y extraer TODOS sus atributos
    member(class(ClassName, Parent, Props, Methods, Instances), CurrentKB),
    
    % 2. Verificar que el objeto no existe
    \+ (member(class(_, _, _, _, AllInstances), CurrentKB),
        member([id=>ObjectName|_], AllInstances)),
    
    % 3. Crear nueva instancia
    NewInstance = [id=>ObjectName, [], []],
    
    % 4. Reemplazar MANTENIENDO TODOS los atributos originales
    replace_class(ClassName, 
                 class(ClassName, Parent, Props, Methods, [NewInstance|Instances]), % ← Todos los campos preservados
                 CurrentKB, NewKB).
    %save_kb('new_kb_1_1.txt',NewKB).



%--------------------------------------------------
% Añadir propiedad a una clase
%--------------------------------------------------
add_class_property(ClassName, Property, Value, CurrentKB, NewKB) :-
    % Verificar que la clase existe
    member(class(ClassName, Parent, Props, Methods, Instances), CurrentKB),
    
    % Verificar que la propiedad no existe ya
    \+ member(Property=_, Props),
    
    % Añadir la nueva propiedad
    append(Props, [Property=>Value], NewProps),
    
    % Reconstruir la clase con la nueva propiedad
    replace_class(ClassName, 
                class(ClassName, Parent, NewProps, Methods, Instances),
                CurrentKB, NewKB).
    %save_kb('new_kb_1_1.txt',NewKB).                



%--------------------------------------------------
% Añadir propiedad a un objeto
%--------------------------------------------------
add_object_property(ObjectName, Property, Value, CurrentKB, NewKB) :-
    % Encontrar el objeto en cualquier clase
    member(class(ClassName, Parent, Props, Methods, Instances), CurrentKB),
    member([id=>ObjectName|ObjProps], Instances),
    
    % Extraer propiedades actuales del objeto
    (   ObjProps = [CurrentProps, _] -> true
    ;   CurrentProps = []
    ),
    
    % Verificar que la propiedad no existe ya
    \+ member(Property=_, CurrentProps),
    
    % Añadir la nueva propiedad
    append(CurrentProps, [Property=>Value], NewObjectProps),
    
    % Reconstruir el objeto con las nuevas propiedades
    replace_object(ObjectName, 
                 [id=>ObjectName, NewObjectProps, []],
                 Instances, NewInstances),
    
    % Actualizar la clase con el objeto modificado
    replace_class(ClassName,
                class(ClassName, Parent, Props, Methods, NewInstances),
                CurrentKB, NewKB).
    %save_kb('new_kb_1_1.txt',NewKB).


%--------------------------------------------------
% Añadir relación entre clases
%--------------------------------------------------
add_class_relation(ClassName, RelationName, RelatedClasses, CurrentKB, NewKB) :-
    % Verificar que la clase existe
    member(class(ClassName, Parent, Props, Methods, Instances), CurrentKB),
    
    % Verificar que las clases relacionadas existen
    forall(member(RelatedClass, RelatedClasses), 
           member(class(RelatedClass, _, _, _, _), CurrentKB)),
    
    % Construir el término de relación
    RelationTerm =.. [RelationName|RelatedClasses],
    
    % Añadir la relación a los métodos (usamos Methods para relaciones)
    append(Methods, [RelationTerm], NewMethods),
    
    % Reconstruir la clase con la nueva relación
    replace_class(ClassName, 
                class(ClassName, Parent, Props, NewMethods, Instances),
                CurrentKB, NewKB).
    %save_kb('new_kb_1_1.txt',NewKB).


%--------------------------------------------------
% Añadir relación entre objetos
%--------------------------------------------------
add_object_relation(ObjectName, RelationName, RelatedObjects, CurrentKB, NewKB) :-
    % Encontrar el objeto en cualquier clase
    member(class(ClassName, Parent, Props, Methods, Instances), CurrentKB),
    member([id=>ObjectName, ObjProps, ObjRelations], Instances),
    
    % Verificar que los objetos relacionados existen
    forall(member(RelatedObj, RelatedObjects),
           (member(class(_, _, _, _, AllInstances), CurrentKB),
            member([id=>RelatedObj|_], AllInstances))),
    
    % Construir el término de relación
    RelationTerm =.. [RelationName|RelatedObjects],
    
    % Añadir la relación al objeto
    append(ObjRelations, [RelationTerm], NewObjRelations),
    
    % Reconstruir el objeto con las nuevas relaciones
    replace_object(ObjectName, 
                 [id=>ObjectName, ObjProps, NewObjRelations],
                 Instances, NewInstances),
    
    % Actualizar la clase con el objeto modificado
    replace_class(ClassName,
                class(ClassName, Parent, Props, Methods, NewInstances),
                CurrentKB, NewKB).
    %save_kb('new_kb_1_1.txt',NewKB).

%-------------------------------------------------------
% Predicados para eliminar:  
%-------------------------------------------------------

% Eliminar una clase
%--------------------------------------------------
% Eliminar una clase (y todos sus objetos)
%--------------------------------------------------
rm_class(ClassName, CurrentKB, NewKB) :-
    % Verificar que la clase existe
    member(class(ClassName, _, _, _, _), CurrentKB),
    
    % Eliminar la clase y sus instancias
    exclude(is_class(ClassName), CurrentKB, TempKB),
    
    % Eliminar objetos de esta clase en otras relaciones
    clean_class_references(ClassName, TempKB, NewKB).

% Predicado auxiliar para filtrar clases
is_class(ClassName, class(ClassName, _, _, _, _)).

% Limpiar referencias a objetos de la clase eliminada
clean_class_references(_, [], []).
clean_class_references(ClassName, [class(C,P,Props,Methods,Instances)|Rest], 
                      [class(C,P,Props,NewMethods,NewInstances)|NewRest]) :-
    % Limpiar relaciones en métodos
    clean_relations(ClassName, Methods, NewMethods),
    
    % Limpiar relaciones en instancias
    clean_object_relations(ClassName, Instances, NewInstances),
    
    % Continuar con el resto
    clean_class_references(ClassName, Rest, NewRest).


%--------------------------------------------------
% Eliminar un objeto
%--------------------------------------------------
rm_object(ObjectName, CurrentKB, NewKB) :-
    % Encontrar y eliminar el objeto de su clase
    remove_object_from_class(ObjectName, CurrentKB, TempKB),
    
    % Eliminar referencias al objeto en otras relaciones
    clean_object_references(ObjectName, TempKB, NewKB).

% Eliminar objeto de su clase contenedora
remove_object_from_class(ObjectName, CurrentKB, NewKB) :-
    findall(
        class(C,P,Props,Methods,NewInstances),
        (member(class(C,P,Props,Methods,Instances), CurrentKB),
         exclude(is_object(ObjectName), Instances, NewInstances)),
        NewKB
    ).

% Predicado auxiliar para filtrar objetos
is_object(ObjectName, [id=>ObjectName|_]).

% Limpiar referencias al objeto eliminado
clean_object_references(_, [], []).
clean_object_references(ObjectName, [class(C,P,Props,Methods,Instances)|Rest], 
                       [class(C,P,Props,NewMethods,NewInstances)|NewRest]) :-
    % Limpiar relaciones en métodos
    clean_object_in_relations(ObjectName, Methods, NewMethods),
    
    % Limpiar relaciones en instancias
    clean_object_in_object_relations(ObjectName, Instances, NewInstances),
    
    % Continuar con el resto
    clean_object_references(ObjectName, Rest, NewRest).

% Limpiar relaciones de clase
clean_relations(ClassName, Methods, NewMethods) :-
    exclude(mentions_class(ClassName), Methods, NewMethods).

mentions_class(ClassName, Relation) :-
    Relation =.. [_|Args],
    member(ClassName, Args).

% Limpiar relaciones en objetos
clean_object_relations(ClassName, Instances, NewInstances) :-
    findall(
        [id=>Obj,Props,NewRels],
        (member([id=>Obj,Props,Rels], Instances),
         exclude(mentions_class(ClassName), Rels, NewRels)),
        NewInstances
    ).

% Limpiar referencias a objetos específicos
clean_object_in_relations(ObjectName, Methods, NewMethods) :-
    exclude(mentions_object(ObjectName), Methods, NewMethods).

mentions_object(ObjectName, Relation) :-
    Relation =.. [_|Args],
    member(ObjectName, Args).

clean_object_in_object_relations(ObjectName, Instances, NewInstances) :-
    findall(
        [id=>Obj,Props,NewRels],
        (member([id=>Obj,Props,Rels], Instances),
         exclude(mentions_object(ObjectName), Rels, NewRels)),
        NewInstances
    ).


%--------------------------------------------------
% Eliminar propiedad de una clase
%--------------------------------------------------
rm_class_property(ClassName, Property, CurrentKB, NewKB) :-
    % Verificar que la clase existe
    member(class(ClassName, Parent, Props, Methods, Instances), CurrentKB),
    
    % Verificar que la propiedad existe
    member(Property=_, Props),
    
    % Eliminar la propiedad
    select(Property=_, Props, NewProps),
    
    % Reconstruir la clase sin la propiedad
    replace_class(ClassName, 
                class(ClassName, Parent, NewProps, Methods, Instances),
                CurrentKB, NewKB).

%--------------------------------------------------
% Eliminar propiedad de un objeto
%--------------------------------------------------
rm_object_property(ObjectName, Property, CurrentKB, NewKB) :-
    % Encontrar el objeto en cualquier clase
    member(class(ClassName, Parent, Props, Methods, Instances), CurrentKB),
    member([id=>ObjectName, ObjProps, ObjRels], Instances),
    
    % Verificar que la propiedad existe en el objeto
    member(Property=_, ObjProps),
    
    % Eliminar la propiedad
    select(Property=_, ObjProps, NewObjProps),
    
    % Reconstruir el objeto sin la propiedad
    replace_object(ObjectName, 
                 [id=>ObjectName, NewObjProps, ObjRels],
                 Instances, NewInstances),
    
    % Actualizar la clase con el objeto modificado
    replace_class(ClassName,
                class(ClassName, Parent, Props, Methods, NewInstances),
                CurrentKB, NewKB).

%--------------------------------------------------
% Eliminar relación específica de una clase
%--------------------------------------------------
rm_class_relation(ClassName, RelationName, CurrentKB, NewKB) :-
    % Verificar que la clase existe
    member(class(ClassName, Parent, Props, Methods, Instances), CurrentKB),
    
    % Eliminar todas las relaciones con este nombre
    exclude(is_relation(RelationName), Methods, NewMethods),
    
    % Reconstruir la clase sin las relaciones
    replace_class(ClassName, 
                class(ClassName, Parent, Props, NewMethods, Instances),
                CurrentKB, NewKB).

% Predicado auxiliar para identificar relaciones
is_relation(RelationName, Relation) :-
    functor(Relation, RelationName, _).

%--------------------------------------------------
% Eliminar relación específica de un objeto
%--------------------------------------------------
rm_object_relation(ObjectName, RelationName, CurrentKB, NewKB) :-
    % Encontrar el objeto en cualquier clase
    member(class(ClassName, Parent, Props, Methods, Instances), CurrentKB),
    member([id=>ObjectName, ObjProps, ObjRels], Instances),
    
    % Eliminar todas las relaciones con este nombre
    exclude(is_relation(RelationName), ObjRels, NewObjRels),
    
    % Reconstruir el objeto sin las relaciones
    replace_object(ObjectName, 
                 [id=>ObjectName, ObjProps, NewObjRels],
                 Instances, NewInstances),
    
    % Actualizar la clase con el objeto modificado
    replace_class(ClassName,
                class(ClassName, Parent, Props, Methods, NewInstances),
                CurrentKB, NewKB).

%--------------------------------------------------
% Cambiar nombre de una clase (y actualizar referencias)
%--------------------------------------------------
change_class_name(OldName, NewName, CurrentKB, NewKB) :-
    % Verificar que la clase existe y el nuevo nombre no
    member(class(OldName, _, _, _, _), CurrentKB),
    \+ member(class(NewName, _, _, _, _), CurrentKB),
    
    % Cambiar nombre en la definición de la clase
    replace_class_name(OldName, NewName, CurrentKB, TempKB),
    
    % Actualizar referencias en herencia
    update_parent_references(OldName, NewName, TempKB, TempKB2),
    
    % Actualizar referencias en relaciones
    update_class_relations(OldName, NewName, TempKB2, NewKB).

% Predicado auxiliar para cambiar el nombre en la definición
replace_class_name(OldName, NewName, [class(OldName, P, Pr, M, I)|Rest], 
                   [class(NewName, P, Pr, M, I)|NewRest]) :-
    replace_class_name(OldName, NewName, Rest, NewRest).
replace_class_name(OldName, NewName, [Class|Rest], [Class|NewRest]) :-
    Class = class(Name, _, _, _, _),
    Name \= OldName,
    replace_class_name(OldName, NewName, Rest, NewRest).
replace_class_name(_, _, [], []).

% Actualizar referencias como clase padre
update_parent_references(OldName, NewName, [class(C, OldName, Pr, M, I)|Rest], 
                         [class(C, NewName, Pr, M, I)|NewRest]) :-
    update_parent_references(OldName, NewName, Rest, NewRest).
update_parent_references(OldName, NewName, [class(C, P, Pr, M, I)|Rest], 
                         [class(C, P, Pr, M, I)|NewRest]) :-
    P \= OldName,
    update_parent_references(OldName, NewName, Rest, NewRest).
update_parent_references(_, _, [], []).

% Actualizar referencias en relaciones
update_class_relations(OldName, NewName, CurrentKB, NewKB) :-
    findall(
        class(C, P, Pr, NewMethods, I),
        (member(class(C, P, Pr, Methods, I), CurrentKB),
         update_relations_in_methods(OldName, NewName, Methods, NewMethods)),
        NewKB
    ).

update_relations_in_methods(_, _, [], []).
update_relations_in_methods(OldName, NewName, [Relation|Rest], [NewRelation|NewRest]) :-
    Relation =.. [RelName|Args],
    replace_in_args(OldName, NewName, Args, NewArgs),
    NewRelation =.. [RelName|NewArgs],
    update_relations_in_methods(OldName, NewName, Rest, NewRest).

replace_in_args(Old, New, [Old|Rest], [New|NewRest]) :-
    replace_in_args(Old, New, Rest, NewRest).
replace_in_args(Old, New, [X|Rest], [X|NewRest]) :-
    X \= Old,
    replace_in_args(Old, New, Rest, NewRest).
replace_in_args(_, _, [], []).

%--------------------------------------------------
% Cambiar nombre de un objeto (y actualizar referencias)
%--------------------------------------------------
change_object_name(OldName, NewName, CurrentKB, NewKB) :-
    % Verificar que el objeto existe y el nuevo nombre no
    (member(class(_, _, _, _, Instances), CurrentKB),
     member([id=>OldName|_], Instances)),
    \+ (member(class(_, _, _, _, AllInstances), CurrentKB),
        member([id=>NewName|_], AllInstances)),
    
    % Cambiar nombre en la definición del objeto
    replace_object_name(OldName, NewName, CurrentKB, TempKB),
    
    % Actualizar referencias en relaciones
    update_object_relations(OldName, NewName, TempKB, NewKB).

% Predicado auxiliar para cambiar el nombre en la definición
replace_object_name(OldName, NewName, [class(C, P, Pr, M, Instances)|Rest], 
                   [class(C, P, Pr, M, NewInstances)|NewRest]) :-
    replace_objects_in_list(OldName, NewName, Instances, NewInstances),
    replace_object_name(OldName, NewName, Rest, NewRest).
replace_object_name(_, _, [], []).

replace_objects_in_list(OldName, NewName, [[id=>OldName|Rest]|More], 
                       [[id=>NewName|Rest]|NewMore]) :-
    replace_objects_in_list(OldName, NewName, More, NewMore).
replace_objects_in_list(OldName, NewName, [Obj|More], [Obj|NewMore]) :-
    Obj = [id=>Name|_],
    Name \= OldName,
    replace_objects_in_list(OldName, NewName, More, NewMore).
replace_objects_in_list(_, _, [], []).

% Actualizar referencias en relaciones
update_object_relations(OldName, NewName, CurrentKB, NewKB) :-
    findall(
        class(C, P, Pr, M, NewInstances),
        (member(class(C, P, Pr, M, Instances), CurrentKB),
         update_relations_in_instances(OldName, NewName, Instances, NewInstances)),
        NewKB
    ).

update_relations_in_instances(OldName, NewName, Instances, NewInstances) :-
    findall(
        [id=>Obj, Props, NewRels],
        (member([id=>Obj, Props, Rels], Instances),
         update_relations_in_list(OldName, NewName, Rels, NewRels)),
        NewInstances
    ).

update_relations_in_list(OldName, NewName, [Relation|Rest], [NewRelation|NewRest]) :-
    Relation =.. [RelName|Args],
    replace_in_args(OldName, NewName, Args, NewArgs),
    NewRelation =.. [RelName|NewArgs],
    update_relations_in_list(OldName, NewName, Rest, NewRest).
update_relations_in_list(_, _, [], []).

%--------------------------------------------------
% replace_object/4 - Reemplazar objeto en una lista de instancias
%--------------------------------------------------
replace_object(_, _, [], []).
replace_object(ObjectName, NewObject, [[id=>ObjectName|_]|Rest], [NewObject|Rest]).
replace_object(ObjectName, NewObject, [Obj|Rest], [Obj|NewRest]) :-
    Obj = [id=>Name|_],
    Name \= ObjectName,
    replace_object(ObjectName, NewObject, Rest, NewRest).

% Reemplazar una clase en la KB
replace_class(_, _, [], []) :- !.
replace_class(ClassName, NewClass, [class(ClassName,_,_,_,_)|Rest], [NewClass|Rest]) :- !.
replace_class(ClassName, NewClass, [Class|Rest], [Class|NewRest]) :-
    replace_class(ClassName, NewClass, Rest, NewRest).        



