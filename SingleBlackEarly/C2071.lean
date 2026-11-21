import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2071 : checkSingleBlackFast2 (-81, -57) 15511 .west (27, 38) (-57, 19) = true := by
  decide +kernel

end LangtonsAnt
