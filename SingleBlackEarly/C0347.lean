import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0347 : checkSingleBlackFast2 (-5, 12) 17183 .west (-7, -4) (-25, -25) = true := by
  decide +kernel

end LangtonsAnt
