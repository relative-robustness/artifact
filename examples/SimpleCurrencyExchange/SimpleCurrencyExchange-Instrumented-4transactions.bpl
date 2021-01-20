// Simple Currency Exchange Application
// It has 4 transactions 
// The save trade transaction is an SQL insert this why the assume must always execute together with the writes (i.e., CAS)

type Pid;
type Uid;
type Tid;

function {:builtin "MapConst"} MapConstBool(bool) : [Uid]bool;
function {:inline} {:linear "uid"} UidCollector(x: Uid) : [Uid]bool
{
  MapConstBool(false)[x := true]
}

function {:builtin "MapConst"} MapConstBool2(bool) : [Tid]bool;
function {:inline} {:linear "tid"} TidCollector(x: Tid) : [Tid]bool
{
  MapConstBool2(false)[x := true]
}

function {:builtin "MapConst"} MapConstBool3(bool) : [Pid]bool;
function {:inline} {:linear "pid"} PidCollector(x: Pid) : [Pid]bool
{
  MapConstBool3(false)[x := true]
}

// shared variables
var {:layer 0,2} tradeContents: [Tid][int]int;
var {:layer 0,2} tradeUser: [Tid]Uid;

// constants 
const unique cstCurFr  :int;   // currency from
const unique cstCurTo  :int;   // currency to
const unique cstsAmt   :int;   // 
const unique cstbAmt   :int;   // 
const unique cstRate   :int;
const unique cstTiPl   :int;
const unique cstoCount :int;

const unique NoUser : Uid;

//////////////////////////////////////////////
// Auxiliary variables for the instrumentation:
//////////////////////////////////////////////

// secondary shared variables to simulate disabled writes and reads

var {:layer 0,2} copytradeContents: [Tid][int]int;
var {:layer 0,2} copytradeUser: [Tid]Uid;

var {:layer 0,2} hb : bool;
var {:layer 0,2} att : bool;

var {:layer 0,2} hbd: [Pid][int][Tid]int;  // hbd[pid][1] for the tradeUser table
										  // hbd[pid][2] for the tradeContents table

var {:layer 0,2} varAtt1 : Tid;

const unique lda, sta: int;

axiom ((lda == 1) && (sta == 2));

const unique attPid : Pid;
const unique helperPid : Pid;

const unique tid0 : Tid;
const unique tid1 : Tid;
const unique tid2 : Tid;

axiom ((tid0 != tid1) && (tid0 != tid2) && (tid1 != tid2));

const unique TNIL0: Tid;

////////////////////////////////////////////////////////////////////////////////
// Procedure of a process
////////////////////////////////////////////////////////////////////////////////
	
procedure {:yields} {:layer 2} process({:linear "pid"} pid:Pid, {:linear "uid"} uid:Uid, {:linear "tid"} tid:Tid)
requires {:layer 2} ((pid == attPid && tid == tid0) || (pid == helperPid && tid == tid1));
{

     var cpTradeContent0     : [int]int;
     var cpTradeUser0   : Uid;
     var timeTrade0  : int;
     var curFr0:int, curTo0:int, sAmt0:int, bAmt0:int, rate0:int, tiPl0:int, oCount0:int;


    yield;
    call Init();
    assert  {:layer 2}   (att == false);
    assert  {:layer 2}   (hb == false);
    assert  {:layer 2}   (forall tid4:Tid, pid0: Pid ::  hbd[pid0][1][tid4] == 0 && hbd[pid0][2][tid4] == 0);
   
    yield;	
    assert {:layer 2}  (forall tid4:Tid ::  hbd[helperPid][1][tid4] == 0 && hbd[helperPid][2][tid4] == 0);	
    assert {:layer 2}  ( hbd[attPid][1][tid1] == 0 && hbd[attPid][2][tid1] == 0);
	  assert  {:layer 2} (pid == attPid ==> !att);
    assert  {:layer 2} (pid == helperPid ==> !hb);
	  assert  {:layer 2} (!att ==> (forall tid4:Tid, pid0: Pid ::  hbd[pid0][1][tid4] == 0 && hbd[pid0][2][tid4] == 0));
	
	if(*)
    {       
		assert {:layer 2}  (forall tid4:Tid ::  hbd[helperPid][1][tid4] == 0 && hbd[helperPid][2][tid4] == 0);	
	  assert  {:layer 2} (pid == attPid ==> !att);
    assert  {:layer 2} (pid == helperPid ==> !hb);
    assert {:layer 2}  ( hbd[attPid][1][tid1] == 0 && hbd[attPid][2][tid1] == 0);
	  assert  {:layer 2} (!att ==> (forall tid4:Tid, pid0: Pid ::  hbd[pid0][1][tid4] == 0 && hbd[pid0][2][tid4] == 0));

	    call SaveTrade(pid, uid,  tid, curFr0, curTo0, sAmt0, bAmt0, rate0, tiPl0, oCount0);
		
    assert {:layer 2}  (hbd[attPid][1][tid1] == 0 && hbd[attPid][2][tid1] == 0);
		assert {:layer 2}  (forall tid4:Tid ::  hbd[helperPid][1][tid4] == 0 && hbd[helperPid][2][tid4] == 0);	
    assert  {:layer 2} (pid == helperPid ==> !hb);
	  assert  {:layer 2} (!att ==> (forall tid4:Tid, pid0: Pid ::  hbd[pid0][1][tid4] == 0 && hbd[pid0][2][tid4] == 0));
    }
    yield;
    assert {:layer 2}  ( hbd[attPid][1][tid1] == 0 && hbd[attPid][2][tid1] == 0);
    assert  {:layer 2} (pid == helperPid ==> !hb);
    assert {:layer 2}  (forall tid4:Tid ::  hbd[helperPid][1][tid4] == 0 && hbd[helperPid][2][tid4] == 0);		

	   call  cpTradeContent0 := ViewTrade(pid, uid,  tid);

    assert {:layer 2}  (hbd[attPid][1][tid1] == 0 && hbd[attPid][2][tid1] == 0);
    assert  {:layer 2} (pid == helperPid ==> !hb);
    assert {:layer 2}  (forall tid4:Tid ::  hbd[helperPid][1][tid4] == 0 && hbd[helperPid][2][tid4] == 0);	
    
	
    yield;
    assert {:layer 2}  ( hbd[attPid][1][tid1] == 0 && hbd[attPid][2][tid1] == 0);
    assert  {:layer 2} (pid == helperPid ==> !hb);
    assert {:layer 2}  (forall tid4:Tid ::  hbd[helperPid][1][tid4] == 0 && hbd[helperPid][2][tid4] == 0);	
	
    if(*)
    {
      assert {:layer 2}  ( hbd[attPid][1][tid1] == 0 && hbd[attPid][2][tid1] == 0);
      assert  {:layer 2} (pid == helperPid ==> !hb);
      assert {:layer 2}  (forall tid4:Tid ::  hbd[helperPid][1][tid4] == 0 && hbd[helperPid][2][tid4] == 0);	
		   
	    call  timeTrade0 :=  GetTradeTimeStamp(pid, uid,  tid);
      
      assert {:layer 2}  ( hbd[attPid][1][tid1] == 0 && hbd[attPid][2][tid1] == 0);
      assert  {:layer 2} (pid == helperPid ==> !hb);
      assert {:layer 2}  (forall tid4:Tid ::  hbd[helperPid][1][tid4] == 0 && hbd[helperPid][2][tid4] == 0);	
    }
	yield;

    assert {:layer 2}  ( hbd[attPid][1][tid1] == 0 && hbd[attPid][2][tid1] == 0);
    assert  {:layer 2} (pid == helperPid ==> !hb);
		assert {:layer 2}  (forall tid4:Tid ::  hbd[helperPid][1][tid4] == 0 && hbd[helperPid][2][tid4] == 0);	
	
    if(*)
    {
      assert {:layer 2}  ( hbd[attPid][1][tid1] == 0 && hbd[attPid][2][tid1] == 0);
      assert  {:layer 2} (pid == helperPid ==> !hb);
      assert {:layer 2}  (forall tid4:Tid ::  hbd[helperPid][1][tid4] == 0 && hbd[helperPid][2][tid4] == 0);		
		   
		call  cpTradeUser0 :=  ViewTradeUser(pid, uid,  tid);

     assert {:layer 2}  (forall tid4:Tid ::  hbd[helperPid][1][tid4] == 0 && hbd[helperPid][2][tid4] == 0);		
    }
    yield;
}

///////////////////////////////////////////////////////////////////////////////
/// An init procedure for initializing the auxiliary variables
///////////////////////////////////////////////////////////////////////////////

procedure  {:atomic} {:layer 2}  init()
{
  assume !hb;
  assume (varAtt1 == TNIL0 && !att);
  assume (forall tid:Tid, pid:Pid ::  hbd[pid][1][tid] == 0 && hbd[pid][2][tid] == 0) ; 
  
}
  
procedure  {:yields} {:layer 1} {:refines "init"}  Init();
ensures {:layer 1} !hb;
ensures {:layer 1} (varAtt1 == TNIL0 && !att);
ensures {:layer 1} (forall tid:Tid, pid:Pid ::  hbd[pid][1][tid] == 0 && hbd[pid][2][tid] == 0) ;

///////////////////////////////////////////////////////////////////////////////
/// The instrumented SimpleCurrencyExchange transactions
///////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}  saveTrade({:linear "pid"} pid:Pid, {:linear "uid"} uid:Uid,  {:linear "tid"} tid: Tid, curFr:int, curTo:int, sAmt:int, bAmt:int, rate:int, tiPl:int, oCount:int)
modifies tradeUser, tradeContents;
modifies copytradeUser, copytradeContents;
modifies hbd, att, hb, varAtt1;
{     
   assume(uid != NoUser);
   assume(tradeUser[tid] == NoUser);

  if (pid == attPid && !att)
	{ 			
    varAtt1 := tid;	
		att := true;

    copytradeUser[tid] := uid;
   
    copytradeContents[tid][cstCurFr] := curFr;
    copytradeContents[tid][cstCurTo] := curTo;
    copytradeContents[tid][cstsAmt] := sAmt;
    copytradeContents[tid][cstbAmt] := bAmt;
    copytradeContents[tid][cstRate]:= rate;
    copytradeContents[tid][cstTiPl] := tiPl;
    copytradeContents[tid][cstoCount] := oCount;
	}
  else if((pid == helperPid) && !hb && att && (hbd[attPid][1][tid] >= lda || hbd[attPid][2][tid] >= lda))
  {
    hb := true;				
		hbd[pid][1][tid] := sta;	
    hbd[pid][2][tid] := sta;	

    tradeUser[tid] := uid;
   
    tradeContents[tid][cstCurFr] := curFr;
    tradeContents[tid][cstCurTo] := curTo;
    tradeContents[tid][cstsAmt] := sAmt;
    tradeContents[tid][cstbAmt] := bAmt;
    tradeContents[tid][cstRate]:= rate;
    tradeContents[tid][cstTiPl] := tiPl;
    tradeContents[tid][cstoCount] := oCount;
  }	
	else 
	{

    tradeUser[tid] := uid;
   
    tradeContents[tid][cstCurFr] := curFr;
    tradeContents[tid][cstCurTo] := curTo;
    tradeContents[tid][cstsAmt] := sAmt;
    tradeContents[tid][cstbAmt] := bAmt;
    tradeContents[tid][cstRate]:= rate;
    tradeContents[tid][cstTiPl] := tiPl;
    tradeContents[tid][cstoCount] := oCount;
	}
   
}
procedure{:yields}{:layer 1} {:refines "saveTrade"} SaveTrade({:linear "pid"} pid:Pid, {:linear "uid"} uid:Uid, {:linear "tid"} tid: Tid, curFr:int, curTo:int, sAmt:int, bAmt:int, rate:int, tiPl:int, oCount:int);

///////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2} viewTrade({:linear "pid"} pid:Pid, {:linear "uid"} uid:Uid, tid: Tid) returns (cpTradeContent:[int]int)
modifies hbd;
{
  assume(uid != NoUser);
  assume(tradeUser[tid] != NoUser);

  if ((pid == attPid && att) || ((pid == helperPid) && hb && att))
	{ 			
    hbd[pid][2][tid] := lda;		
		cpTradeContent := tradeContents[tid];	
	}			
	else 
	{
		cpTradeContent := tradeContents[tid];
	}
}
procedure {:yields}{:layer 1} {:refines "viewTrade"} ViewTrade({:linear "pid"} pid:Pid, {:linear "uid"} uid:Uid, tid: Tid) returns (cpTradeContent:[int]int);

///////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2} viewTradeUser({:linear "pid"} pid:Pid, {:linear "uid"} uid:Uid, tid: Tid) returns (cpTradeUser:Uid)
modifies hbd;
{
  assume(uid != NoUser);
  assume(tradeUser[tid] != NoUser);

  if ((pid == attPid && att) || ((pid == helperPid) && hb && att))
	{ 			
    hbd[pid][1][tid] := lda;		
		cpTradeUser := tradeUser[tid]; 			
	}			
	else 
	{
		cpTradeUser := tradeUser[tid]; 
	}
}
procedure {:yields}{:layer 1} {:refines "viewTradeUser"} ViewTradeUser({:linear "pid"} pid:Pid, {:linear "uid"} uid:Uid, tid: Tid) returns (cpTradeUser:Uid);

///////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2} getTradeTimeStamp({:linear "pid"} pid:Pid, {:linear "uid"} uid:Uid, tid: Tid) returns (timeTrade:int)
modifies hbd;
{
  assume(uid != NoUser);
  assume(tradeUser[tid] != NoUser);

  if ((pid == attPid && att) || ((pid == helperPid) && hb && att))
	{ 			
    hbd[pid][2][tid] := lda;		
		timeTrade:=tradeContents[tid][cstTiPl]; 			
	}			
	else 
	{
		timeTrade:=tradeContents[tid][cstTiPl]; 
	} 
}
procedure {:yields}{:layer 1} {:refines "getTradeTimeStamp"} GetTradeTimeStamp({:linear "pid"} pid:Pid, {:linear "uid"} uid:Uid, tid: Tid) returns (timeTrade:int);
