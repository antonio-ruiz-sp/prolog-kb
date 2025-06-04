:- module(debug, [start/1, stop/2, log/2]).

% start/1: Starts a debug session with a given SessionName.
start(SessionName) :-
    format('Debug session "~w" started.~n', [SessionName]).

% stop/2: Stops a debug session with a given SessionName and Reason.
stop(SessionName, Reason) :-
    format('Debug session "~w" stopped. Reason: ~w~n', [SessionName, Reason]).

% log/2: Logs a Message under a given SessionName.
log(SessionName, Message) :-
    format('[~w] LOG: ~w~n', [SessionName, Message]).