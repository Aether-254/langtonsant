import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2067 : checkSingleBlackFast2 (-80, -57) 15407 .west (27, 37) (-56, 17) = true := by
  decide +kernel

end LangtonsAnt
