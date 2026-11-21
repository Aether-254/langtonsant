import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1162 : checkSingleBlackFast2 (26, -19) 12176 .north (-4, 4) (-28, 6) = true := by
  decide +kernel

end LangtonsAnt
