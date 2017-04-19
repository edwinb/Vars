module HTTPMessage

import Control.ST

public export
data ReqType = GET String | POST String -- Just support the basics...

public export
data Connection = KeepAlive | Close

public export
record HTTPContent where
  constructor MkContent
  keep : Connection
  header : List (String, String)
  content : String

public export
record HTTPRequest where
  constructor MkReq
  reqType : ReqType
  version : String
  content : HTTPContent

public export
data RespCode = MkCode Int

public export
record HTTPResponse where
  constructor MkResponse
  code : RespCode
  version : String
  content : HTTPContent

export
parseRequest : String -> Maybe HTTPRequest
parseRequest _ = Nothing

public export
HTTPProc : (Type -> Type) -> Type
HTTPProc m = HTTPRequest -> ST m HTTPResponse []

public export
Show HTTPResponse where
  show x = ?show_rhs

