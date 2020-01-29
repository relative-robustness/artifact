// FusionTicket Application
// We assume each event is provided with a unique identifier,
// Thus, the addEvent behaves like SQL insert
// RUN: %boogie -noinfer -typeEncoding:m -trace -errorTrace:2 -useArrayTheory "%FusionTicketInstrumented.bpl" > "%FusionTicketInstrumented.bpl.solution"



type Pid;
type Eid;   // Event identifier type
type Vid;  //  Venue identifier type

function {:builtin "MapConst"} MapConstBool(bool) : [Pid]bool;
function {:inline} {:linear "pid"} TidCollector(x: Pid) : [Pid]bool
{
  MapConstBool(false)[x := true]
}

// shared variables
var   {:layer 0,2} EventsByVenue        : [Vid][Eid]bool;	
var   {:layer 0,2} EventNbTicket        : [Vid][Eid]int;


  
procedure  {:atomic}{:layer 2} browse(pid:Pid, venueId0:Vid) returns (eventsId:[Eid]bool)
{  	   
	eventsId := EventsByVenue[venueId0];    			
}
procedure  {:yields} {:layer 1} {:refines "browse"}  Browse(pid:Pid,venueId0:Vid) returns (eventsId:[Eid]bool);



procedure {:atomic}{:layer 2}  purchaseTicket(pid:Pid, eventId0:Eid, venueId0: Vid) returns (price:int)
modifies  EventNbTicket;
{      
	   
	assume (EventsByVenue[venueId0][eventId0]);
    assume  EventNbTicket[venueId0][eventId0] > 0;

	EventNbTicket[venueId0][eventId0] := EventNbTicket[venueId0][eventId0] - 1;

	if (EventNbTicket[venueId0][eventId0] > 50)  
  	{
		price := 17;
  	} 
  	else  
  	{ 
  		price := 27;
  	}
}
procedure  {:yields} {:layer 1} {:refines "purchaseTicket"}  PurchaseTicket(pid:Pid, eventId0:Eid, venueId0: Vid) returns (price:int);
		ensures {:layer 1} ((EventNbTicket[venueId0][eventId0] == old(EventNbTicket[venueId0][eventId0]) - 1) );


procedure {:atomic}{:layer 2} addEvent(pid:Pid, eventId0:Eid, venueId0:Vid) 
modifies EventsByVenue, EventNbTicket;
{     
  var nbTicket                 : int;
     
  assume nbTicket > 0;

  assume !EventsByVenue[venueId0][eventId0] ; 

  EventsByVenue[venueId0][eventId0] := true;
   
  EventNbTicket[venueId0][eventId0] := nbTicket;   	
}
procedure  {:yields} {:layer 1} {:refines "addEvent"}  AddEvent(pid:Pid, eventId0:Eid, venueId0:Vid);
ensures  {:layer 1} ((EventsByVenue[venueId0][eventId0] == true && EventNbTicket[venueId0][eventId0] > 0) );
