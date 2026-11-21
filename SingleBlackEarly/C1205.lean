import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1205 : checkSingleBlackFast (23, 4) 14812 .north (-4, 2) (-28, 4) = true := by
  decide +kernel

end LangtonsAnt
