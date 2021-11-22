include Base

module Monad = struct
  include Base.Monad
  include Misc.Monad
end

module Size = Misc.Size
module Sized_list = Misc.Sized_list