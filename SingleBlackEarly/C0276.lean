import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0276 : checkSingleBlackFast2 (15, 9) 22245 .east (1, -11) (-23, -28) = true := by
  decide +kernel

end LangtonsAnt
