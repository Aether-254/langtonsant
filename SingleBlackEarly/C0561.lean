import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0561 : checkSingleBlackFast (20, -5) 7277 .west (-23, 0) (-14, -24) = true := by
  decide +kernel

end LangtonsAnt
