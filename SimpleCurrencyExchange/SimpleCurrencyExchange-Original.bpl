// Simple Currency Exchange Application
// A trade can be accessed by only the process that added it

type Uid;
type Tid;

function {:builtin "MapConst"} MapConstBool(bool) : [Tid]bool;
function {:inline} {:linear "tid"} TidCollector(x: Tid) : [Tid]bool
{
  MapConstBool(false)[x := true]
}


// shared variables
var {:layer 0,2} tradeContents: [Tid][int]int;
var {:layer 0,2} tradeUser: [Tid]Uid;

// constants 
const unique cstCurFr:int;
const unique cstCurTo  :int; 
const unique cstsAmt   :int;
const unique cstbAmt   :int;
const unique cstRate   :int;
const unique cstTiPl   :int;
const unique cstoCount :int;


procedure {:atomic}{:layer 2}  saveTrade({:linear "tid"} tid:Tid, uid:Uid, curFr:int, curTo:int, sAmt:int, bAmt:int, rate:int, tiPl:int, oCount:int)
modifies tradeUser, tradeContents;
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
procedure{:yields}{:layer 1} {:refines "saveTrade"} SaveTrade({:linear "tid"} tid:Tid, uid:Uid, curFr:int, curTo:int, sAmt:int, bAmt:int, rate:int, tiPl:int, oCount:int);


procedure {:atomic}{:layer 2} viewTrade({:linear "tid"} tid:Tid) returns (cpTradeContent:[int]int)
{
  cpTradeContent := tradeContents[tid];
}
procedure {:yields}{:layer 1} {:refines "viewTrade"} ViewTrade({:linear "tid"} tid:Tid) returns (cpTradeContent:[int]int);


procedure {:atomic}{:layer 2} viewTradeUser({:linear "tid"} tid:Tid) returns (cpTradeUser:Uid)
{
  cpTradeUser := tradeUser[tid]; 
}
procedure {:yields}{:layer 1} {:refines "viewTradeUser"} ViewTradeUser({:linear "tid"} tid:Tid) returns (cpTradeUser:Uid);


procedure {:atomic}{:layer 2} getTradeTimeStamp({:linear "tid"} tid:Tid) returns (timeTrade:int)
{
  timeTrade:=tradeContents[tid][cstTiPl]; 
}
procedure {:yields}{:layer 1} {:refines "getTradeTimeStamp"} GetTradeTimeStamp({:linear "tid"} tid:Tid) returns (timeTrade:int);
