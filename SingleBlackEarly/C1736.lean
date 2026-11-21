import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1736 : checkSingleBlackFast2 (-49, -27) 15273 .west (12, 21) (-41, 1) = true := by
  decide +kernel

end LangtonsAnt
