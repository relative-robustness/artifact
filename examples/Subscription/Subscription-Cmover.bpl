// Subscription Application

type Pid;
type Uid;

function {:builtin "MapConst"} MapConstBool(bool) : [Pid]bool;
function {:inline} {:linear "pid"} TidCollector(x: Pid) : [Pid]bool
{
  MapConstBool(false)[x := true]
}

function {:builtin "MapConst"} MapConstBool2(bool) : [Uid]bool;
function {:inline} {:linear "uid"} TidCollector2(x: Uid) : [Uid]bool
{
  MapConstBool2(false)[x := true]
}

var {:layer 0,2} ActiveUser: [Uid]bool;
var {:layer 0,2} UserPassword: [Uid]int;


procedure {:right}{:layer 2}  addUserR(uid:Uid, p: int)
{  
  assume (!ActiveUser[uid] && UserPassword[uid] == 0 && p != 0);
}
procedure{:yields}{:layer 1} {:refines "addUserR"} AddUserR(uid:Uid, p: int);


procedure {:right}{:layer 2}  addUserW(uid:Uid, p: int)
modifies ActiveUser, UserPassword;
{      
	ActiveUser[uid] := true; 
  UserPassword[uid] := p;
}
procedure{:yields}{:layer 1} {:refines "addUserW"} AddUserW(uid:Uid, p: int);


procedure {:right}{:layer 2}  removeUserR({:linear "uid"} uid:Uid)
{  
  assume (ActiveUser[uid] && UserPassword[uid] != 0);
}
procedure{:yields}{:layer 1} {:refines "removeUserR"} RemoveUserR({:linear "uid"} uid:Uid);


procedure {:right}{:layer 2}  removeUserW({:linear "uid"} uid:Uid)
modifies ActiveUser, UserPassword;
{  
	ActiveUser[uid] := false; 
  UserPassword[uid] := -1;
}
procedure{:yields}{:layer 1} {:refines "removeUserW"} RemoveUserW({:linear "uid"} uid:Uid);
