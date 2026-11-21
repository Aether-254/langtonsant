import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0426 : checkSingleBlackFast (19, 1) 6163 .west (-15, 7) (-18, -17) = true := by
  decide +kernel

end LangtonsAnt
