import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0087 : checkSingleBlackFast (4, 2) 7109 .west (7, 2) (-18, -6) = true := by
  decide +kernel

end LangtonsAnt
