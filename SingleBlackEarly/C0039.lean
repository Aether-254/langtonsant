import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0039 : checkSingleBlackFast (-1, 4) 2603 .west (-2, -3) (-16, -6) = true := by
  decide +kernel

end LangtonsAnt
