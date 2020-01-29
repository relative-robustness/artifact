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

// secondary shared variables to simulate disabled writes and reads

var   {:layer 0,2} copyEventsByVenue        : [Vid][Eid]bool;	
var   {:layer 0,2} copyEventNbTicket        : [Vid][Eid]int;



// 
var {:layer 0,2} hb : bool;


var {:layer 0,2} att : bool;

var {:layer 0,2} hbd: [int][Vid][Eid]int;  // hbd[1] for the EventNbTicket table
										  // hbd[2] for the EventsByVenue table


var {:layer 0,2} varAtt1 : Vid;
var {:layer 0,2} varAtt2 : Eid;


const unique lda, sta: int;

axiom ((lda == 1) && (sta == 2));


const unique attPid : Pid;
const unique helperPid : Pid;

const unique VNIL0: Vid;
const unique ENIL0: Eid;


function {:builtin "((as const (Array Int (Array Int Int))) 0)"} I0() returns ([Vid][Eid] int);
function {:builtin "((as const (Array Int (Array Int Bool))) False)"} I1() returns ([Vid][Eid] bool);
function {:builtin "((as const (Array Int (Array Int (Array Int Bool)))) False)"} I2() returns ([Vid][Eid][Pid] bool);

//  Process session	
	
procedure {:yields} {:layer 2} process({:linear "pid"} pid:Pid)
requires {:layer 2} (pid == attPid || pid == helperPid);
{

     var venueId0:Vid, eventId0:Eid;
     var eventsId0     : [Eid]bool;
     var evNbTicket0   : int;
     var ticketPrice0  : int;


    assume (eventId0 != ENIL0 && venueId0 != VNIL0);

   
    yield;
    call Init();
    assert  {:layer 2}   (att == false);
    assert  {:layer 2}   (hb == false);
    assert  {:layer 2}   (forall venueId:Vid, eventId:Eid:: hbd[1][venueId][eventId] == 0 &&  hbd[2][venueId][eventId] == 0);

   
    yield;
	assert {:layer 2}  (pid == attPid ==> hbd[1][varAtt1][varAtt2] != sta);
	assert {:layer 2}  (pid == helperPid ==> hbd[1][varAtt1][varAtt2] != sta);	
	assert  {:layer 2} (pid == attPid ==> !att);
	assert  {:layer 2} (!att ==> (forall venueId:Vid, eventId:Eid:: hbd[1][venueId][eventId] == 0 &&  hbd[2][venueId][eventId] == 0));
	
	
    if(*)
    {       
	   assert {:layer 2}  (pid == attPid ==> hbd[1][varAtt1][varAtt2] != sta);
	   assert {:layer 2}  (pid == helperPid ==> hbd[1][varAtt1][varAtt2] != sta);	

	   call  ticketPrice0 := PurchaseTicket(pid,eventId0,venueId0);

	   assert {:layer 2}  (pid == attPid ==> hbd[1][varAtt1][varAtt2] != sta);
	   assert {:layer 2}  (pid == helperPid ==> hbd[1][varAtt1][varAtt2] != sta);	           
    }
    yield;
}

procedure  {:atomic} {:layer 2}  init()
{
  assume !hb;
  assume (varAtt1 == VNIL0 && varAtt2 == ENIL0 && !att);
  assume (forall eventId:Eid, venueId:Vid::  hbd[1][venueId][eventId] == 0 && hbd[2][venueId][eventId] == 0) ; 
  
}
  
procedure  {:yields} {:layer 1} {:refines "init"}  Init();
ensures {:layer 1} !hb;
ensures {:layer 1} (varAtt1 == VNIL0 && varAtt2 == ENIL0 && !att);
ensures {:layer 1} (forall eventId:Eid, venueId:Vid::  hbd[1][venueId][eventId] == 0 && hbd[2][venueId][eventId] == 0) ;




procedure  {:atomic}{:layer 2} browse(pid:Pid, venueId0:Vid) returns (eventsId:[Eid]bool)
{  	   
	eventsId := EventsByVenue[venueId0];    			
}
procedure  {:yields} {:layer 1} {:refines "browse"}  Browse(pid:Pid,venueId0:Vid) returns (eventsId:[Eid]bool);



procedure {:atomic}{:layer 2}  purchaseTicket(pid:Pid, eventId0:Eid, venueId0: Vid) returns (price:int)
modifies  EventNbTicket;
modifies copyEventNbTicket;
modifies hb, hbd, att, varAtt1, varAtt2;
{      
	   
	   assume (EventsByVenue[venueId0][eventId0]);
       assume  EventNbTicket[venueId0][eventId0] > 0;
   	
	  if (pid == attPid && !att)
	  { 
			
		copyEventNbTicket[venueId0][eventId0] := EventNbTicket[venueId0][eventId0] - 1;
			
		if (copyEventNbTicket[venueId0][eventId0] > 50)  
			{
				price := 17;
			} 
			else  
			{ 
				price := 27;
			}   
		
		hbd[1][venueId0][eventId0] := lda;
		
		varAtt1 := venueId0;
		varAtt2 := eventId0;	
		att := true;	
			
	  }			

	else if ((pid == helperPid) && att && !hb)
	{								
		assume (hbd[1][venueId0][eventId0] >= lda);
	
		hb := true;
		
		EventNbTicket[venueId0][eventId0] := EventNbTicket[venueId0][eventId0] - 1;
   
		if (EventNbTicket[venueId0][eventId0] > 50)  
		{
			price := 17;
		} 
		else  
		{ 
			price := 27;
		}

		hbd[1][venueId0][eventId0] := sta;
	}

	else 
	{
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

}
procedure  {:yields} {:layer 1} {:refines "purchaseTicket"}  PurchaseTicket(pid:Pid, eventId0:Eid, venueId0: Vid) returns (price:int);
		ensures {:layer 1} ((EventNbTicket[venueId0][eventId0] == old(EventNbTicket[venueId0][eventId0]) - 1) || (copyEventNbTicket[venueId0][eventId0] == EventNbTicket[venueId0][eventId0] - 1));


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
