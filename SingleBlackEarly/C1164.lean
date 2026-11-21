import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1164 : checkSingleBlackFast2 (25, -20) 10816 .north (-4, 2) (-28, 4) = true := by
  decide +kernel

end LangtonsAnt
