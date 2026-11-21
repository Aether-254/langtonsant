import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0085 : checkSingleBlackFast (3, 3) 1919 .west (-3, 0) (-13, -5) = true := by
  decide +kernel

end LangtonsAnt
