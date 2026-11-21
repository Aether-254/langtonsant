import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0832 : checkSingleBlackFast2 (21, 2) 11988 .north (-7, 5) (-1, -23) = true := by
  decide +kernel

end LangtonsAnt
