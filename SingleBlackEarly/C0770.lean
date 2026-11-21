import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0770 : checkSingleBlackFast (21, -15) 5819 .west (-12, 6) (-19, -14) = true := by
  decide +kernel

end LangtonsAnt
