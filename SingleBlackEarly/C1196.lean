import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1196 : checkSingleBlackFast2 (27, 4) 10908 .north (-4, 0) (-28, 2) = true := by
  decide +kernel

end LangtonsAnt
