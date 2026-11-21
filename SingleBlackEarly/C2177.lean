import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2177 : checkSingleBlackFast2 (-90, -67) 15927 .west (32, 42) (-61, 22) = true := by
  decide +kernel

end LangtonsAnt
