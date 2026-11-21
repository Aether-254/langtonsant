import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2005 : checkSingleBlackFast2 (-75, -51) 15199 .west (24, 35) (-54, 16) = true := by
  decide +kernel

end LangtonsAnt
