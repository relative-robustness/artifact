// FusionTicket Application 
// It has 3 transactions
// We assume each event regardless of the venue is provided with a unique identifier, thus the addEvent behaves like an SQL insert 
// Non-robustness check between CC and PC
// RUN: /usr/bin/time -v --format="%e" %boogie -noinfer -typeEncoding:m -tracePOs -traceTimes  -trace  -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Pid;
type Eid;   // Event identifier type
type Vid;  //  Venue identifier type

function {:builtin "MapConst"} MapConstBool(bool) : [Pid]bool;
function {:inline} {:linear "pid"} PidCollector(x: Pid) : [Pid]bool
{
  MapConstBool(false)[x := true]
}

// shared variables
var   {:layer 0,2} EventsByVenue        : [Vid][Eid]bool;	
var   {:layer 0,2} EventNbTicket        : [Vid][Eid]int;

//////////////////////////////////////////////
// Auxiliary variables for the instrumentation:
//////////////////////////////////////////////

// secondary shared variables to simulate disabled writes and reads

var   {:layer 0,2} copyEventsByVenue        : [Vid][Eid]bool;	
var   {:layer 0,2} copyEventNbTicket        : [Vid][Eid]int;

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

////////////////////////////////////////////////////////////////////////////////
// Procedure of a process
////////////////////////////////////////////////////////////////////////////////
	
procedure {:yields} {:layer 2} process({:linear "pid"} pid:Pid)
requires {:layer 2} (pid == attPid || pid == helperPid);
{

     var venueId0:Vid, venueId1:Vid, eventId0:Eid, eventId1:Eid;
     var eventsId0     : [Eid]bool;
     var evNbTicket0   : int;
     var ticketPrice0  : int;

	assume (eventId1 != eventId0);
    assume (eventId0 != ENIL0 && venueId0 != VNIL0 && eventId1 != ENIL0 && venueId1 != VNIL0);
   
    yield;
    call Init();
    assert  {:layer 2}   (att == false);
    assert  {:layer 2}   (hb == false);
    assert  {:layer 2}   (forall venueId:Vid, eventId:Eid:: hbd[1][venueId][eventId] == 0 && 
							hbd[2][venueId][eventId] == 0);
   
    yield;
	assert {:layer 2}  (pid == attPid ==> hbd[2][varAtt1][varAtt2] != lda);
	assert {:layer 2}  (pid == helperPid ==> hbd[2][varAtt1][varAtt2] != lda);	
	assert  {:layer 2} (pid == attPid ==> !att);
	assert  {:layer 2} (!att ==> (forall venueId:Vid, eventId:Eid:: hbd[1][venueId][eventId] == 0 &&  
									hbd[2][venueId][eventId] == 0));
	
	if(pid == attPid)
    {       
		assert {:layer 2}  (pid == attPid ==> hbd[2][varAtt1][varAtt2] != lda);
	    assert {:layer 2}  (pid == helperPid ==> hbd[2][varAtt1][varAtt2] != lda);		
		assert  {:layer 2} (pid == attPid ==> !att);
	    assert  {:layer 2} (!att ==> (forall venueId:Vid, eventId:Eid:: hbd[1][venueId][eventId] == 0 && 
							hbd[2][venueId][eventId] == 0));

	    call AddEvent(pid,eventId0,venueId0);
		
		assert {:layer 2}  (pid == attPid ==> hbd[2][varAtt1][varAtt2] != lda);
	    assert {:layer 2}  (pid == helperPid ==> hbd[2][varAtt1][varAtt2] != lda);		
    }
    yield;
	assert {:layer 2}  (pid == attPid ==> hbd[2][varAtt1][varAtt2] != lda);
	assert {:layer 2}  (pid == helperPid ==> hbd[2][varAtt1][varAtt2] != lda);	
	
	
    if(*)
    {       
	   assert {:layer 2}  (pid == attPid ==> hbd[2][varAtt1][varAtt2] != lda);
	   assert {:layer 2}  (pid == helperPid ==> hbd[2][varAtt1][varAtt2] != lda);	

	   call  ticketPrice0 := PurchaseTicket(pid,eventId1,venueId1);

	   assert {:layer 2}  (pid == attPid ==> hbd[2][varAtt1][varAtt2] != lda);
	   assert {:layer 2}  (pid == helperPid ==> hbd[2][varAtt1][varAtt2] != lda);	           
    }
	
    yield;
		assert {:layer 2}  (pid == attPid ==> hbd[2][varAtt1][varAtt2] != lda);
	    assert {:layer 2}  (pid == helperPid ==> hbd[2][varAtt1][varAtt2] != lda);		
	
    if(pid == helperPid)
    {
		assert {:layer 2}  (pid == attPid ==> hbd[2][varAtt1][varAtt2] != lda);
	    assert {:layer 2}  (pid == helperPid ==> hbd[2][varAtt1][varAtt2] != lda);		
		   
	    call  eventsId0 :=  Browse(pid,venueId0);

        assert {:layer 2}  (pid == attPid ==> hbd[2][varAtt1][varAtt2] != lda);
	    assert {:layer 2}  (pid == helperPid ==> hbd[2][varAtt1][varAtt2] != lda);	
    }
    yield;
}

///////////////////////////////////////////////////////////////////////////////
/// An init procedure for initializing the auxiliary variables
///////////////////////////////////////////////////////////////////////////////

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

///////////////////////////////////////////////////////////////////////////////
/// The instrumented FusionTicket transactions
///////////////////////////////////////////////////////////////////////////////

procedure  {:atomic}{:layer 2} browse(pid:Pid, venueId0:Vid) returns (eventsId:[Eid]bool)
modifies hbd;
{  
    var hbd1, hbd2 : [Vid][Eid]int;	
	
    if (att && pid == helperPid && hb)
	{		
		hbd1 := hbd[2];
		hbd[2]  := hbd2;
		
		assume ((forall venueId:Vid:: venueId != venueId0 ==> 
		        (forall eventId:Eid:: hbd[2][venueId][eventId] == hbd1[venueId][eventId])) && 
				(forall eventId:Eid:: (hbd1[venueId0][eventId] == 0 ==> hbd[2][venueId0][eventId] == lda) && 
			    (hbd1[venueId0][eventId] != 0 ==> hbd[2][venueId0][eventId] == hbd1[venueId0][eventId])));												
	}
	   
	eventsId := EventsByVenue[venueId0];    			
}
procedure  {:yields} {:layer 1} {:refines "browse"}  Browse(pid:Pid,venueId0:Vid) returns (eventsId:[Eid]bool);

///////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}  purchaseTicket(pid:Pid, eventId0:Eid, venueId0: Vid) returns (price:int)
modifies  EventNbTicket;
modifies copyEventNbTicket;
modifies hb, hbd;
{      
	   
	   assume (EventsByVenue[venueId0][eventId0]);
       assume  EventNbTicket[venueId0][eventId0] > 0;
   	
	  if (pid == attPid && att)
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
		
		hbd[1][venueId0][eventId0] := sta;
			
	  }			

	else if ((pid == helperPid) && !hb)
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
		ensures {:layer 1} ((EventNbTicket[venueId0][eventId0] == old(EventNbTicket[venueId0][eventId0]) - 1) || 
							(copyEventNbTicket[venueId0][eventId0] == EventNbTicket[venueId0][eventId0] - 1));

///////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2} addEvent(pid:Pid, eventId0:Eid, venueId0:Vid) 
modifies EventsByVenue, EventNbTicket;
modifies copyEventsByVenue, copyEventNbTicket;
modifies varAtt1, varAtt2;
modifies att;
{   
    
	var nbTicket                 : int;
     
   assume nbTicket > 0;

   assume !EventsByVenue[venueId0][eventId0] ; 
	
	if (pid == attPid && !att)
	{
		copyEventsByVenue[venueId0][eventId0] := true;
		
		copyEventNbTicket[venueId0][eventId0] := nbTicket; 
		
		varAtt1 := venueId0;
		varAtt2 := eventId0;	
		att := true;	
			
	}	
	else 
	{
  		EventsByVenue[venueId0][eventId0] := true;
   
   		EventNbTicket[venueId0][eventId0] := nbTicket;   
	}		
}
procedure  {:yields} {:layer 1} {:refines "addEvent"}  AddEvent(pid:Pid, eventId0:Eid, venueId0:Vid);
ensures  {:layer 1} ((EventsByVenue[venueId0][eventId0] == true && EventNbTicket[venueId0][eventId0] > 0) || 
                     (copyEventsByVenue[venueId0][eventId0] == true && copyEventNbTicket[venueId0][eventId0] > 0));
