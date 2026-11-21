import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2150 : checkSingleBlackFast (-89, -62) 20290 .north (36, 29) (-63, -42) = true := by
  decide +kernel

end LangtonsAnt
