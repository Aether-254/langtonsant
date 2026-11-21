import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1182 : checkSingleBlackFast2 (25, 0) 12040 .north (-4, 0) (-28, 2) = true := by
  decide +kernel

end LangtonsAnt
